/*
  Copyright 2015 Google LLC All rights reserved.

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at:

    http://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.
*/

/*
   american fuzzy lop - LLVM-mode instrumentation pass
   ---------------------------------------------------

   Written by Laszlo Szekeres <lszekeres@google.com> and
              Michal Zalewski <lcamtuf@google.com>

   LLVM integration design comes from Laszlo Szekeres. C bits copied-and-pasted
   from afl-as.c are Michal's fault.

   This library is plugged into LLVM when invoking clang through afl-clang-fast.
   It tells the compiler to add code roughly equivalent to the bits discussed
   in ../afl-as.h.
*/

#define AFL_LLVM_PASS

#include "../config.h"
#include "../debug.h"

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

#include <vector>
#include <unordered_map>
#include <unordered_set>
#include <fstream>

#include <boost/graph/adjacency_list.hpp>
#include <boost/graph/graph_traits.hpp>
#include <boost/graph/dijkstra_shortest_paths.hpp>
namespace bo = boost;

#include "llvm/ADT/Statistic.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/Debug.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/Support/CommandLine.h"

#if defined(LLVM34)
#include "llvm/DebugInfo.h"
#else
#include "llvm/IR/DebugInfo.h"
#endif

#if defined(LLVM34) || defined(LLVM35) || defined(LLVM36)
#define LLVM_OLD_DEBUG_API
#endif

using namespace llvm;

cl::opt<std::string> TargetsFile(
    "targets",
    cl::desc("Input file containing the target lines of code."),
    cl::value_desc("targets"));

namespace {

  class AFLCoverage : public ModulePass {

    public:

      static char ID;
      AFLCoverage() : ModulePass(ID) { }

      bool runOnModule(Module &M) override;

      // StringRef getPassName() const override {
      //  return "American Fuzzy Lop Instrumentation";
      // }

  };

}


char AFLCoverage::ID = 0;

namespace {

static bool isBlacklisted(const Function *F) {

  static const SmallVector<std::string, 8> Blacklist = {
    "asan.",
    "__asan",
    "llvm.",
    "sancov.",
    "__ubsan_handle_",
    "free",
    "malloc",
    "calloc",
    "realloc"
  };

  for (auto const &BlacklistFunc : Blacklist) {
    if (F->getName().startswith(BlacklistFunc)) {
      return true;
    }
  }

  return false;
}

using Weight = size_t;
using Property = bo::property<bo::edge_weight_t, Weight>;
using Graph = bo::adjacency_list<
  bo::vecS, bo::vecS, bo::directedS, bo::no_property,
  Property>;
using Vertex = bo::graph_traits<Graph>::vertex_descriptor;
using Edge = std::pair<Vertex, Vertex>;

/*
Given function f, we get all outgoing edges with weight according to its CFG.
We should note same callee function can appear in different call sites.
*/
std::unordered_map<Function*, size_t> getOutEdges(Function& F) {

  using namespace std;

  // Array of all basic blocks, index is the ID (e.g. Vertex).
  vector<BasicBlock*> blocks;
  // Map each block to assigned ID (e.i. index in blocks) and set of callees in it.
  unordered_map<BasicBlock*, pair<unordered_set<Function*>, Vertex>> block_info;

  // Assign each block in CFG with an ID
  for (auto& BB : F) {

    unordered_set<Function*> callees; // Functions called in this block.

    for (auto& I : BB) {

      if (auto *c = dyn_cast<CallInst>(&I)) {

        if (Function *CalledF = c->getCalledFunction()) {

          if (!isBlacklisted(CalledF) && CalledF->begin() != CalledF->end())
            callees.insert(CalledF);

        }

      }

    }

    block_info.emplace(&BB,make_pair<unordered_set<Function*>, Vertex>(
                                      std::move(callees), blocks.size()));
    blocks.push_back(&BB);

  }

  // Construct CFG of the function
  vector<Edge> edges; vector<Weight> weights;
  for (auto& BB : F) {

    Vertex u = block_info.find(&BB)->second.second;

    Instruction* Term = BB.getTerminator();
    unsigned n = Term->getNumSuccessors();
    for (unsigned i = 0; i < n; ++i) {
      Vertex v = block_info.find(Term->getSuccessor(i))->second.second;
      edges.emplace_back(u, v);
      weights.push_back(n == 1 ? 0 : 1); // If not branch, weight is zero.
    }

  }

  // Dijskra from function entrypoint.
  size_t num_blocks = blocks.size();
  unique_ptr<Weight[]> d = make_unique<Weight[]>(num_blocks);
  unique_ptr<Vertex[]> p = make_unique<Vertex[]>(num_blocks);
  Graph cfg(edges.begin(), edges.end(), weights.begin(), num_blocks);
  assert(bo::num_vertices(cfg) == num_blocks);
  Vertex entry = block_info.find(&F.getEntryBlock())->second.second;
  dijkstra_shortest_paths(cfg, entry,
    bo::predecessor_map(p.get()).distance_map(d.get()));

  unordered_map<Function*, size_t> out_edges;
  // For each basic blocks, we get its callees, and update edge if possible.
  bo::graph_traits<Graph>::vertex_iterator vi, vend;
  for (bo::tie(vi, vend) = bo::vertices(cfg); vi != vend; ++vi) {

    // Skip unreachable vertexes
    if (p[*vi] == *vi && *vi != entry)
      continue;

    const auto& callees = block_info.find(blocks[*vi])->second.first;

    for (Function* Callee : callees) {

      // If mutitple blocks call same function, we get minimum weight of them.
      auto it = out_edges.emplace(Callee, d[*vi]).first;
      it->second = min(it->second, d[*vi]);

    }

  }

  return out_edges;

}

/* Obtain Call graph with weight, which is obtained using getOutEdges. */
std::tuple<Graph, std::vector<Function*>, std::unordered_map<Function*, Vertex>>
  getCallGraph(Module& M) {

  using namespace std;
  vector<Function*> functions;
  unordered_map<Function*, Vertex> func_to_id;
  for (auto& F : M) {

    if (isBlacklisted(&F) || F.begin() == F.end())
      continue;

    func_to_id.emplace(&F, functions.size());
    functions.push_back(&F);

  }

  vector<Edge> edges; vector<Weight> weights;
  for (const auto& func_id : func_to_id) {

    auto out_edges = getOutEdges(*func_id.first);
    for (const auto& edge : out_edges) {

      // Inverse the edge.
      edges.emplace_back(func_to_id.find(edge.first)->second, func_id.second);
      weights.push_back(edge.second);

    }

  }

  return make_tuple<Graph, vector<Function*>, unordered_map<Function*, Vertex>>(
    Graph(edges.begin(), edges.end(), weights.begin(), functions.size()),
    std::move(functions), std::move(func_to_id));

}

std::unordered_set<std::string> parseTargets() {
  using namespace std;
  unordered_set<string> targets;
  if (TargetsFile.empty())
    return targets;
  ifstream targetsfile(TargetsFile); assert(targetsfile.is_open());
  string line;
  while (getline(targetsfile, line)) {
    size_t found = line.find_last_of("/\\");
    if (found != string::npos)
      line = line.substr(found + 1);
    targets.insert(line);
  }
  targetsfile.close();
  return targets;
}

static void getDebugLoc(const Instruction *I, std::string &Filename,
                        unsigned &Line) {
#ifdef LLVM_OLD_DEBUG_API
  DebugLoc Loc = I->getDebugLoc();
  if (!Loc.isUnknown()) {
    DILocation cDILoc(Loc.getAsMDNode(M.getContext()));
    DILocation oDILoc = cDILoc.getOrigLocation();

    Line = oDILoc.getLineNumber();
    Filename = oDILoc.getFilename().str();

    if (filename.empty()) {
      Line = cDILoc.getLineNumber();
      Filename = cDILoc.getFilename().str();
    }
  }
#else
  if (DILocation *Loc = I->getDebugLoc()) {
    Line = Loc->getLine();
    Filename = Loc->getFilename().str();

    if (Filename.empty()) {
      DILocation *oDILoc = Loc->getInlinedAt();
      if (oDILoc) {
        Line = oDILoc->getLine();
        Filename = oDILoc->getFilename().str();
      }
    }
  }
#endif /* LLVM_OLD_DEBUG_API */
}


/*
We identify and record each target Block, and Function that contains them.
We also decide the order of targets in this function.
*/
std::vector<std::pair<BasicBlock*, Function*>> getTargetBlocks(Module& M) {

  using namespace std;

  vector<pair<BasicBlock*, Function*>> ret;
  auto targets = parseTargets();
  for (auto& F : M) {

    if (isBlacklisted(&F))
      continue;

    for (auto& BB : F) {

      for (auto& I : BB) {

        string filename; unsigned line = 0;
        getDebugLoc(&I, filename, line);
        static const string Xlibs("/usr/");
        if (filename.empty() || line == 0 ||
          !filename.compare(0, Xlibs.size(), Xlibs))
          continue;

        size_t found = filename.find_last_of("/\\");
        if (found != string::npos)
          filename = filename.substr(found + 1);

        // If instructin debug info is target, we mark the BasicBlock as target.
        if (targets.count(filename + ':' + to_string(line)) > 0) {
          ret.emplace_back(&BB, &F);
          break; // We only append each BasicBlock once.
        }

      }

    }

  }

  return ret;
}

std::unordered_map<Function*, std::vector<std::pair<size_t, Weight>>> getDists(
  Module& M, const std::vector<std::pair<BasicBlock*, Function*>>& targets) {

  Graph cg;
  std::vector<Function*> functions;
  std::unordered_map<Function*, Vertex> func_to_id;
  std::tie(cg, functions, func_to_id) = getCallGraph(M);

  size_t num_functions = functions.size();
  size_t num_targets = targets.size();
  std::unique_ptr<Weight[]> d = std::make_unique<Weight[]>(num_functions);
  std::unique_ptr<Vertex[]> p = std::make_unique<Vertex[]>(num_functions);

  // Map each function to distances from it to each target.
  std::unordered_map<Function*, std::vector<std::pair<size_t, Weight>>> distances;

  for (size_t i = 0; i < num_targets; ++i) {

    Vertex t = func_to_id.find(targets[i].second)->second;
    dijkstra_shortest_paths(cg, t,
      bo::predecessor_map(p.get()).distance_map(d.get()));

    bo::graph_traits<Graph>::vertex_iterator vi, vend;
    for (bo::tie(vi, vend) = bo::vertices(cg); vi != vend; ++vi) {

      if (p[*vi] == *vi && *vi != t)
        continue;

      distances[functions[*vi]].emplace_back(i, d[*vi]);

    }

  }

  return distances;
}

}


bool AFLCoverage::runOnModule(Module &M) {

  LLVMContext &C = M.getContext();

  IntegerType *Int8Ty  = IntegerType::getInt8Ty(C);
  IntegerType *Int32Ty = IntegerType::getInt32Ty(C);
  IntegerType *Int64Ty = IntegerType::getInt64Ty(C);

  /* Show a banner */

  char be_quiet = 0;

  if (isatty(2) && !getenv("AFL_QUIET")) {

    SAYF(cCYA "afl-llvm-pass " cBRI VERSION cRST " by <lszekeres@google.com>\n");

  } else be_quiet = 1;

  /* Decide instrumentation ratio */

  char* inst_ratio_str = getenv("AFL_INST_RATIO");
  unsigned int inst_ratio = 100;

  if (inst_ratio_str) {

    if (sscanf(inst_ratio_str, "%u", &inst_ratio) != 1 || !inst_ratio ||
        inst_ratio > 100)
      FATAL("Bad value of AFL_INST_RATIO (must be between 1 and 100)");

  }

  /* Get globals for the SHM region and the previous location. Note that
     __afl_prev_loc is thread-local. */

  GlobalVariable *AFLMapPtr =
      new GlobalVariable(M, PointerType::get(Int8Ty, 0), false,
                         GlobalValue::ExternalLinkage, 0, "__afl_area_ptr");

  GlobalVariable *AFLPrevLoc = new GlobalVariable(
      M, Int32Ty, false, GlobalValue::ExternalLinkage, 0, "__afl_prev_loc",
      0, GlobalVariable::GeneralDynamicTLSModel, 0, false);

  /* Instrument all the things! */

  int inst_blocks = 0;
  size_t num_funcs = 0;

  for (auto &F : M) {

    if (F.begin() == F.end())
      continue;

    {
      IRBuilder<> IRB(&(*F.getEntryBlock().getFirstInsertionPt()));
      ConstantInt* FuncID = ConstantInt::get(Int64Ty, num_funcs++);
      Type *Args[] = {Int64Ty};
      FunctionType *FTy = FunctionType::get(Type::getVoidTy(C), Args, false);
      IRB.CreateCall(
        M.getOrInsertFunction("fish_each_func_inst", FTy), {FuncID});
    }

    for (auto &BB : F) {

      BasicBlock::iterator IP = BB.getFirstInsertionPt();
      IRBuilder<> IRB(&(*IP));

      if (AFL_R(100) >= inst_ratio) continue;

      /* Make up cur_loc */

      unsigned int cur_loc = AFL_R(MAP_SIZE);

      ConstantInt *CurLoc = ConstantInt::get(Int32Ty, cur_loc);

      /* Load prev_loc */

      LoadInst *PrevLoc = IRB.CreateLoad(AFLPrevLoc);
      PrevLoc->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
      Value *PrevLocCasted = IRB.CreateZExt(PrevLoc, IRB.getInt32Ty());

      /* Load SHM pointer */

      LoadInst *MapPtr = IRB.CreateLoad(AFLMapPtr);
      MapPtr->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
      Value *MapPtrIdx =
          IRB.CreateGEP(MapPtr, IRB.CreateXor(PrevLocCasted, CurLoc));

      /* Update bitmap */

      LoadInst *Counter = IRB.CreateLoad(MapPtrIdx);
      Counter->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
      Value *Incr = IRB.CreateAdd(Counter, ConstantInt::get(Int8Ty, 1));
      IRB.CreateStore(Incr, MapPtrIdx)
          ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

      /* Set prev_loc to cur_loc >> 1 */

      StoreInst *Store =
          IRB.CreateStore(ConstantInt::get(Int32Ty, cur_loc >> 1), AFLPrevLoc);
      Store->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

      inst_blocks++;

    }
  }

  auto targets = getTargetBlocks(M);
  size_t num_targets = targets.size();
  auto dists = getDists(M, targets);

  // Store the number of targets into binary for fuzzer and execution to know it.
  new GlobalVariable(M, Int32Ty, true, GlobalValue::ExternalLinkage,
    ConstantInt::get(Int32Ty, num_targets), "__fish_num_targets");
  new GlobalVariable(M, Int64Ty, true, GlobalValue::ExternalLinkage,
    ConstantInt::get(Int64Ty, num_funcs), "__fish_num_funcs");

  char buf[64];
  int r = snprintf(buf, sizeof(buf), NUM_TARGETS_SIG"%lu", num_targets);
  if (r <= 0 || r >= sizeof(buf))
    FATAL("snprintf error");
  new GlobalVariable(M, ArrayType::get(Int8Ty, r + 1),
    true, GlobalValue::ExternalLinkage,
    ConstantDataArray::getString(C, buf), "__fish_num_targets_str");
  r = snprintf(buf, sizeof(buf), NUM_FUNCS_SIG"%lu", num_funcs);
  if (r <= 0 || r >= sizeof(buf))
    FATAL("snprintf error");
  new GlobalVariable(M, ArrayType::get(Int8Ty, r + 1),
    true, GlobalValue::ExternalLinkage,
    ConstantDataArray::getString(C, buf), "__fish_num_funcs_str");

  // For each target basic block, we call `fish_target_inst(target_id)`.
  for (size_t t = 0; t < num_targets; ++t) {

    const auto& target = targets[t];
    IRBuilder<> IRB(&(*target.first->getFirstInsertionPt()));

    ConstantInt* TargetID = ConstantInt::get(Int32Ty, t);
    Type *Args[] = {Int32Ty};
    FunctionType *FTy = FunctionType::get(Type::getVoidTy(C), Args, false);
    IRB.CreateCall(M.getOrInsertFunction("fish_target_inst", FTy), {TargetID});

  }

  // For each function that can reach at least one target,
  // We have `for (t : targets_reachable(func)) fish_func_inst(t, dist[func, t])`.
  for (const auto& reachable : dists) {

    IRBuilder<> IRB(&(*reachable.first->getEntryBlock().getFirstInsertionPt()));
    Type *Args[] = {Int32Ty, Int64Ty};

    for (const auto& target_dist : reachable.second) {

      ConstantInt* TargetID = ConstantInt::get(Int32Ty, target_dist.first);
      ConstantInt* Dist = ConstantInt::get(Int64Ty, target_dist.second);
      FunctionType *FTy = FunctionType::get(Type::getVoidTy(C), Args, false);
      IRB.CreateCall(
        M.getOrInsertFunction("fish_func_inst", FTy), {TargetID, Dist});

    }

  }

  /* Say something nice. */

  if (!be_quiet) {

    if (!inst_blocks) WARNF("No instrumentation targets found.");
    else OKF("Instrumented %u locations and %lu targets (%s mode, ratio %u%%).",
             inst_blocks, num_targets, getenv("AFL_HARDEN") ? "hardened" :
             ((getenv("AFL_USE_ASAN") || getenv("AFL_USE_MSAN")) ?
              "ASAN/MSAN" : "non-hardened"), inst_ratio);

  }

  return true;

}


static void registerAFLPass(const PassManagerBuilder &,
                            legacy::PassManagerBase &PM) {

  PM.add(new AFLCoverage());

}

static RegisterStandardPasses RegisterAFLPassLTO(
    PassManagerBuilder::EP_FullLinkTimeOptimizationLast, registerAFLPass);

static RegisterStandardPasses RegisterAFLPass0(
    PassManagerBuilder::EP_EnabledOnOptLevel0, registerAFLPass);
