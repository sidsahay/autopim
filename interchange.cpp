//Modified by Siddharth Sahay

 // Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
 // See https://llvm.org/LICENSE.txt for license information.
 // SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

 //
 //
 //===----------------------------------------------------------------------===//
 //
 // This Pass handles loop interchange transform.
 // This pass interchanges loops to provide a more cache-friendly memory access
 // patterns.
 //
 //===----------------------------------------------------------------------===//
 
 #include "llvm/ADT/STLExtras.h"
 #include "llvm/ADT/SmallVector.h"
 #include "llvm/ADT/Statistic.h"
 #include "llvm/ADT/StringRef.h"
 #include "llvm/Analysis/DependenceAnalysis.h"
 #include "llvm/Analysis/LoopInfo.h"
 #include "llvm/Analysis/LoopPass.h"
 #include "llvm/Analysis/OptimizationRemarkEmitter.h"
 #include "llvm/Analysis/ScalarEvolution.h"
 #include "llvm/Analysis/ScalarEvolutionExpressions.h"
 #include "llvm/IR/BasicBlock.h"
 #include "llvm/IR/Constants.h"
 #include "llvm/IR/DiagnosticInfo.h"
 #include "llvm/IR/Dominators.h"
 #include "llvm/IR/Function.h"
 #include "llvm/IR/InstrTypes.h"
 #include "llvm/IR/Instruction.h"
 #include "llvm/IR/Instructions.h"
 #include "llvm/IR/Type.h"
 #include "llvm/IR/User.h"
 #include "llvm/IR/Value.h"
 #include "llvm/Pass.h"
 #include "llvm/Support/Casting.h"
 #include "llvm/Support/CommandLine.h"
 #include "llvm/Support/Debug.h"
 #include "llvm/Support/ErrorHandling.h"
 #include "llvm/Support/raw_ostream.h"
 #include "llvm/Transforms/Scalar.h"
 #include "llvm/Transforms/Utils.h"
 #include "llvm/Transforms/Utils/BasicBlockUtils.h"
 #include "llvm/Transforms/Utils/LoopUtils.h"
 #include <cassert>
 #include <utility>
 #include <vector>
 
 using namespace llvm;
 
 namespace {
 
 using LoopVector = SmallVector<Loop *, 8>;
 
 // TODO: Check if we can use a sparse matrix here.
 using CharMatrix = std::vector<std::vector<char>>;
 
 } // end anonymous namespace
 
 namespace {
 
 /// LoopInterchangeLegality checks if it is legal to interchange the loop.
 class LoopInterchangeLegality {
 public:
   LoopInterchangeLegality(Loop *Outer, Loop *Inner, ScalarEvolution *SE,
                           OptimizationRemarkEmitter *ORE)
       : OuterLoop(Outer), InnerLoop(Inner), SE(SE), ORE(ORE) {}
 
   /// Check if the loops can be interchanged.
   bool canInterchangeLoops(unsigned InnerLoopId, unsigned OuterLoopId,
                            CharMatrix &DepMatrix);
 
   /// Check if the loop structure is understood. We do not handle triangular
   /// loops for now.
   bool isLoopStructureUnderstood(PHINode *InnerInductionVar);
 
   bool currentLimitations();
 
   const SmallPtrSetImpl<PHINode *> &getOuterInnerReductions() const {
     return OuterInnerReductions;
   }
 
 private:
   bool tightlyNested(Loop *Outer, Loop *Inner);
   bool containsUnsafeInstructions(BasicBlock *BB);
 
   /// Discover induction and reduction PHIs in the header of \p L. Induction
   /// PHIs are added to \p Inductions, reductions are added to
   /// OuterInnerReductions. When the outer loop is passed, the inner loop needs
   /// to be passed as \p InnerLoop.
   bool findInductionAndReductions(Loop *L,
                                   SmallVector<PHINode *, 8> &Inductions,
                                   Loop *InnerLoop);
 
   Loop *OuterLoop;
   Loop *InnerLoop;
 
   ScalarEvolution *SE;
 
   /// Interface to emit optimization remarks.
   OptimizationRemarkEmitter *ORE;
 
   /// Set of reduction PHIs taking part of a reduction across the inner and
   /// outer loop.
   SmallPtrSet<PHINode *, 4> OuterInnerReductions;
 };
  
 /// LoopInterchangeTransform interchanges the loop.
 class LoopInterchangeTransform {
 public:
   LoopInterchangeTransform(Loop *Outer, Loop *Inner, ScalarEvolution *SE,
                            LoopInfo *LI, DominatorTree *DT,
                            BasicBlock *LoopNestExit,
                            const LoopInterchangeLegality &LIL)
       : OuterLoop(Outer), InnerLoop(Inner), SE(SE), LI(LI), DT(DT),
         LoopExit(LoopNestExit), LIL(LIL) {}
 
   /// Interchange OuterLoop and InnerLoop.
   bool transform();
   void restructureLoops(Loop *NewInner, Loop *NewOuter,
                         BasicBlock *OrigInnerPreHeader,
                         BasicBlock *OrigOuterPreHeader);
   void removeChildLoop(Loop *OuterLoop, Loop *InnerLoop);
 
 private:
   bool adjustLoopLinks();
   void adjustLoopPreheaders();
   bool adjustLoopBranches();
 
   Loop *OuterLoop;
   Loop *InnerLoop;
 
   /// Scev analysis.
   ScalarEvolution *SE;
 
   LoopInfo *LI;
   DominatorTree *DT;
   BasicBlock *LoopExit;
 
   const LoopInterchangeLegality &LIL;
 };
 
 } // end anonymous namespace
 
 bool LoopInterchangeLegality::containsUnsafeInstructions(BasicBlock *BB) {
   return any_of(*BB, [](const Instruction &I) {
     return I.mayHaveSideEffects() || I.mayReadFromMemory();
   });
 }
 
 bool LoopInterchangeLegality::tightlyNested(Loop *OuterLoop, Loop *InnerLoop) {
   BasicBlock *OuterLoopHeader = OuterLoop->getHeader();
   BasicBlock *InnerLoopPreHeader = InnerLoop->getLoopPreheader();
   BasicBlock *OuterLoopLatch = OuterLoop->getLoopLatch();
 
   LLVM_DEBUG(dbgs() << "Checking if loops are tightly nested\n");
 
   // A perfectly nested loop will not have any branch in between the outer and
   // inner block i.e. outer header will branch to either inner preheader and
   // outerloop latch.
   BranchInst *OuterLoopHeaderBI =
       dyn_cast<BranchInst>(OuterLoopHeader->getTerminator());
   if (!OuterLoopHeaderBI)
     return false;
 
   for (BasicBlock *Succ : successors(OuterLoopHeaderBI))
     if (Succ != InnerLoopPreHeader && Succ != InnerLoop->getHeader() &&
         Succ != OuterLoopLatch)
       return false;
 
   LLVM_DEBUG(dbgs() << "Checking instructions in Loop header and Loop latch\n");
   // We do not have any basic block in between now make sure the outer header
   // and outer loop latch doesn't contain any unsafe instructions.
   if (containsUnsafeInstructions(OuterLoopHeader) ||
       containsUnsafeInstructions(OuterLoopLatch))
     return false;
 
   LLVM_DEBUG(dbgs() << "Loops are perfectly nested\n");
   // We have a perfect loop nest.
   return true;
 }
 
 bool LoopInterchangeLegality::isLoopStructureUnderstood(
     PHINode *InnerInduction) {
   unsigned Num = InnerInduction->getNumOperands();
   BasicBlock *InnerLoopPreheader = InnerLoop->getLoopPreheader();
   for (unsigned i = 0; i < Num; ++i) {
     Value *Val = InnerInduction->getOperand(i);
     if (isa<Constant>(Val))
       continue;
     Instruction *I = dyn_cast<Instruction>(Val);
     if (!I)
       return false;
     // TODO: Handle triangular loops.
     // e.g. for(int i=0;i<N;i++)
     //        for(int j=i;j<N;j++)
     unsigned IncomBlockIndx = PHINode::getIncomingValueNumForOperand(i);
     if (InnerInduction->getIncomingBlock(IncomBlockIndx) ==
             InnerLoopPreheader &&
         !OuterLoop->isLoopInvariant(I)) {
       return false;
     }
   }
   return true;
 }
 
 // If SV is a LCSSA PHI node with a single incoming value, return the incoming
 // value.
 static Value *followLCSSA(Value *SV) {
   PHINode *PHI = dyn_cast<PHINode>(SV);
   if (!PHI)
     return SV;
 
   if (PHI->getNumIncomingValues() != 1)
     return SV;
   return followLCSSA(PHI->getIncomingValue(0));
 }
 
 // Check V's users to see if it is involved in a reduction in L.
 static PHINode *findInnerReductionPhi(Loop *L, Value *V) {
   for (Value *User : V->users()) {
     if (PHINode *PHI = dyn_cast<PHINode>(User)) {
       if (PHI->getNumIncomingValues() == 1)
         continue;
       RecurrenceDescriptor RD;
       if (RecurrenceDescriptor::isReductionPHI(PHI, L, RD))
         return PHI;
       return nullptr;
     }
   }
 
   return nullptr;
 }
 
 bool LoopInterchangeLegality::findInductionAndReductions(
     Loop *L, SmallVector<PHINode *, 8> &Inductions, Loop *InnerLoop) {
   if (!L->getLoopLatch() || !L->getLoopPredecessor())
     return false;
   for (PHINode &PHI : L->getHeader()->phis()) {
     RecurrenceDescriptor RD;
     InductionDescriptor ID;
     if (InductionDescriptor::isInductionPHI(&PHI, L, SE, ID))
       Inductions.push_back(&PHI);
     else {
       // PHIs in inner loops need to be part of a reduction in the outer loop,
       // discovered when checking the PHIs of the outer loop earlier.
       if (!InnerLoop) {
         if (OuterInnerReductions.find(&PHI) == OuterInnerReductions.end()) {
           LLVM_DEBUG(dbgs() << "Inner loop PHI is not part of reductions "
                                "across the outer loop.\n");
           return false;
         }
       } else {
         assert(PHI.getNumIncomingValues() == 2 &&
                "Phis in loop header should have exactly 2 incoming values");
         // Check if we have a PHI node in the outer loop that has a reduction
         // result from the inner loop as an incoming value.
         Value *V = followLCSSA(PHI.getIncomingValueForBlock(L->getLoopLatch()));
         PHINode *InnerRedPhi = findInnerReductionPhi(InnerLoop, V);
         if (!InnerRedPhi ||
             !llvm::any_of(InnerRedPhi->incoming_values(),
                           [&PHI](Value *V) { return V == &PHI; })) {
           LLVM_DEBUG(
               dbgs()
               << "Failed to recognize PHI as an induction or reduction.\n");
           return false;
         }
         OuterInnerReductions.insert(&PHI);
         OuterInnerReductions.insert(InnerRedPhi);
       }
     }
   }
   return true;
 }
 
 static bool containsSafePHI(BasicBlock *Block, bool isOuterLoopExitBlock) {
   for (PHINode &PHI : Block->phis()) {
     // Reduction lcssa phi will have only 1 incoming block that from loop latch.
     if (PHI.getNumIncomingValues() > 1)
       return false;
     Instruction *Ins = dyn_cast<Instruction>(PHI.getIncomingValue(0));
     if (!Ins)
       return false;
     // Incoming value for lcssa phi's in outer loop exit can only be inner loop
     // exits lcssa phi else it would not be tightly nested.
     if (!isa<PHINode>(Ins) && isOuterLoopExitBlock)
       return false;
   }
   return true;
 }
 
 // This function indicates the current limitations in the transform as a result
 // of which we do not proceed.
 bool LoopInterchangeLegality::currentLimitations() {
   BasicBlock *InnerLoopPreHeader = InnerLoop->getLoopPreheader();
   BasicBlock *InnerLoopLatch = InnerLoop->getLoopLatch();
 
   // transform currently expects the loop latches to also be the exiting
   // blocks.
   if (InnerLoop->getExitingBlock() != InnerLoopLatch ||
       OuterLoop->getExitingBlock() != OuterLoop->getLoopLatch() ||
       !isa<BranchInst>(InnerLoopLatch->getTerminator()) ||
       !isa<BranchInst>(OuterLoop->getLoopLatch()->getTerminator())) {
     LLVM_DEBUG(
         dbgs() << "Loops where the latch is not the exiting block are not"
                << " supported currently.\n");
     ORE->emit([&]() {
       return OptimizationRemarkMissed(DEBUG_TYPE, "ExitingNotLatch",
                                       OuterLoop->getStartLoc(),
                                       OuterLoop->getHeader())
              << "Loops where the latch is not the exiting block cannot be"
                 " interchange currently.";
     });
     return true;
   }
 
   PHINode *InnerInductionVar;
   SmallVector<PHINode *, 8> Inductions;
   if (!findInductionAndReductions(OuterLoop, Inductions, InnerLoop)) {
     LLVM_DEBUG(
         dbgs() << "Only outer loops with induction or reduction PHI nodes "
                << "are supported currently.\n");
     ORE->emit([&]() {
       return OptimizationRemarkMissed(DEBUG_TYPE, "UnsupportedPHIOuter",
                                       OuterLoop->getStartLoc(),
                                       OuterLoop->getHeader())
              << "Only outer loops with induction or reduction PHI nodes can be"
                 " interchanged currently.";
     });
     return true;
   }
 
   // TODO: Currently we handle only loops with 1 induction variable.
   if (Inductions.size() != 1) {
     LLVM_DEBUG(dbgs() << "Loops with more than 1 induction variables are not "
                       << "supported currently.\n");
     ORE->emit([&]() {
       return OptimizationRemarkMissed(DEBUG_TYPE, "MultiIndutionOuter",
                                       OuterLoop->getStartLoc(),
                                       OuterLoop->getHeader())
              << "Only outer loops with 1 induction variable can be "
                 "interchanged currently.";
     });
     return true;
   }
 
   Inductions.clear();
   if (!findInductionAndReductions(InnerLoop, Inductions, nullptr)) {
     LLVM_DEBUG(
         dbgs() << "Only inner loops with induction or reduction PHI nodes "
                << "are supported currently.\n");
     ORE->emit([&]() {
       return OptimizationRemarkMissed(DEBUG_TYPE, "UnsupportedPHIInner",
                                       InnerLoop->getStartLoc(),
                                       InnerLoop->getHeader())
              << "Only inner loops with induction or reduction PHI nodes can be"
                 " interchange currently.";
     });
     return true;
   }
 
   // TODO: Currently we handle only loops with 1 induction variable.
   if (Inductions.size() != 1) {
     LLVM_DEBUG(
         dbgs() << "We currently only support loops with 1 induction variable."
                << "Failed to interchange due to current limitation\n");
     ORE->emit([&]() {
       return OptimizationRemarkMissed(DEBUG_TYPE, "MultiInductionInner",
                                       InnerLoop->getStartLoc(),
                                       InnerLoop->getHeader())
              << "Only inner loops with 1 induction variable can be "
                 "interchanged currently.";
     });
     return true;
   }
   InnerInductionVar = Inductions.pop_back_val();
 
   // TODO: Triangular loops are not handled for now.
   if (!isLoopStructureUnderstood(InnerInductionVar)) {
     LLVM_DEBUG(dbgs() << "Loop structure not understood by pass\n");
     ORE->emit([&]() {
       return OptimizationRemarkMissed(DEBUG_TYPE, "UnsupportedStructureInner",
                                       InnerLoop->getStartLoc(),
                                       InnerLoop->getHeader())
              << "Inner loop structure not understood currently.";
     });
     return true;
   }
 
   // TODO: We only handle LCSSA PHI's corresponding to reduction for now.
   BasicBlock *InnerExit = InnerLoop->getExitBlock();
   if (!containsSafePHI(InnerExit, false)) {
     LLVM_DEBUG(
         dbgs() << "Can only handle LCSSA PHIs in inner loops currently.\n");
     ORE->emit([&]() {
       return OptimizationRemarkMissed(DEBUG_TYPE, "NoLCSSAPHIOuterInner",
                                       InnerLoop->getStartLoc(),
                                       InnerLoop->getHeader())
              << "Only inner loops with LCSSA PHIs can be interchange "
                 "currently.";
     });
     return true;
   }
 
   // TODO: Current limitation: Since we split the inner loop latch at the point
   // were induction variable is incremented (induction.next); We cannot have
   // more than 1 user of induction.next since it would result in broken code
   // after split.
   // e.g.
   // for(i=0;i<N;i++) {
   //    for(j = 0;j<M;j++) {
   //      A[j+1][i+2] = A[j][i]+k;
   //  }
   // }
   Instruction *InnerIndexVarInc = nullptr;
   if (InnerInductionVar->getIncomingBlock(0) == InnerLoopPreHeader)
     InnerIndexVarInc =
         dyn_cast<Instruction>(InnerInductionVar->getIncomingValue(1));
   else
     InnerIndexVarInc =
         dyn_cast<Instruction>(InnerInductionVar->getIncomingValue(0));
 
   if (!InnerIndexVarInc) {
     LLVM_DEBUG(
         dbgs() << "Did not find an instruction to increment the induction "
                << "variable.\n");
     ORE->emit([&]() {
       return OptimizationRemarkMissed(DEBUG_TYPE, "NoIncrementInInner",
                                       InnerLoop->getStartLoc(),
                                       InnerLoop->getHeader())
              << "The inner loop does not increment the induction variable.";
     });
     return true;
   }
 
   // Since we split the inner loop latch on this induction variable. Make sure
   // we do not have any instruction between the induction variable and branch
   // instruction.
 
   bool FoundInduction = false;
   for (const Instruction &I :
        llvm::reverse(InnerLoopLatch->instructionsWithoutDebug())) {
     if (isa<BranchInst>(I) || isa<CmpInst>(I) || isa<TruncInst>(I) ||
         isa<ZExtInst>(I))
       continue;
 
     // We found an instruction. If this is not induction variable then it is not
     // safe to split this loop latch.
     if (!I.isIdenticalTo(InnerIndexVarInc)) {
       LLVM_DEBUG(dbgs() << "Found unsupported instructions between induction "
                         << "variable increment and branch.\n");
       ORE->emit([&]() {
         return OptimizationRemarkMissed(
                    DEBUG_TYPE, "UnsupportedInsBetweenInduction",
                    InnerLoop->getStartLoc(), InnerLoop->getHeader())
                << "Found unsupported instruction between induction variable "
                   "increment and branch.";
       });
       return true;
     }
 
     FoundInduction = true;
     break;
   }
   // The loop latch ended and we didn't find the induction variable return as
   // current limitation.
   if (!FoundInduction) {
     LLVM_DEBUG(dbgs() << "Did not find the induction variable.\n");
     ORE->emit([&]() {
       return OptimizationRemarkMissed(DEBUG_TYPE, "NoIndutionVariable",
                                       InnerLoop->getStartLoc(),
                                       InnerLoop->getHeader())
              << "Did not find the induction variable.";
     });
     return true;
   }
   return false;
 }
 
 // We currently support LCSSA PHI nodes in the outer loop exit, if their
 // incoming values do not come from the outer loop latch or if the
 // outer loop latch has a single predecessor. In that case, the value will
 // be available if both the inner and outer loop conditions are true, which
 // will still be true after interchanging. If we have multiple predecessor,
 // that may not be the case, e.g. because the outer loop latch may be executed
 // if the inner loop is not executed.
 static bool areLoopExitPHIsSupported(Loop *OuterLoop, Loop *InnerLoop) {
   BasicBlock *LoopNestExit = OuterLoop->getUniqueExitBlock();
   for (PHINode &PHI : LoopNestExit->phis()) {
     //  FIXME: We currently are not able to detect floating point reductions
     //         and have to use floating point PHIs as a proxy to prevent
     //         interchanging in the presence of floating point reductions.
     if (PHI.getType()->isFloatingPointTy())
       return false;
     for (unsigned i = 0; i < PHI.getNumIncomingValues(); i++) {
      Instruction *IncomingI = dyn_cast<Instruction>(PHI.getIncomingValue(i));
      if (!IncomingI || IncomingI->getParent() != OuterLoop->getLoopLatch())
        continue;
 
      // The incoming value is defined in the outer loop latch. Currently we
      // only support that in case the outer loop latch has a single predecessor.
      // This guarantees that the outer loop latch is executed if and only if
      // the inner loop is executed (because tightlyNested() guarantees that the
      // outer loop header only branches to the inner loop or the outer loop
      // latch).
      // FIXME: We could weaken this logic and allow multiple predecessors,
      //        if the values are produced outside the loop latch. We would need
      //        additional logic to update the PHI nodes in the exit block as
      //        well.
      if (OuterLoop->getLoopLatch()->getUniquePredecessor() == nullptr)
        return false;
     }
   }
   return true;
 }
 
  
  void LoopInterchangeTransform::removeChildLoop(Loop *OuterLoop,
                                                Loop *InnerLoop) {
   for (Loop *L : *OuterLoop)
     if (L == InnerLoop) {
       OuterLoop->removeChildLoop(L);
       return;
     }
   llvm_unreachable("Couldn't find loop");
 }
 
 /// Update LoopInfo, after interchanging. NewInner and NewOuter refer to the
 /// new inner and outer loop after interchanging: NewInner is the original
 /// outer loop and NewOuter is the original inner loop.
 ///
 /// Before interchanging, we have the following structure
 /// Outer preheader
 //  Outer header
 //    Inner preheader
 //    Inner header
 //      Inner body
 //      Inner latch
 //   outer bbs
 //   Outer latch
 //
 // After interchanging:
 // Inner preheader
 // Inner header
 //   Outer preheader
 //   Outer header
 //     Inner body
 //     outer bbs
 //     Outer latch
 //   Inner latch
 void LoopInterchangeTransform::restructureLoops(
     Loop *NewInner, Loop *NewOuter, BasicBlock *OrigInnerPreHeader,
     BasicBlock *OrigOuterPreHeader) {
   Loop *OuterLoopParent = OuterLoop->getParentLoop();
   // The original inner loop preheader moves from the new inner loop to
   // the parent loop, if there is one.
   NewInner->removeBlockFromLoop(OrigInnerPreHeader);
   LI->changeLoopFor(OrigInnerPreHeader, OuterLoopParent);
 
   // Switch the loop levels.
   if (OuterLoopParent) {
     // Remove the loop from its parent loop.
     removeChildLoop(OuterLoopParent, NewInner);
     removeChildLoop(NewInner, NewOuter);
     OuterLoopParent->addChildLoop(NewOuter);
   } else {
     removeChildLoop(NewInner, NewOuter);
     LI->changeTopLevelLoop(NewInner, NewOuter);
   }
   while (!NewOuter->empty())
     NewInner->addChildLoop(NewOuter->removeChildLoop(NewOuter->begin()));
   NewOuter->addChildLoop(NewInner);
 
   // BBs from the original inner loop.
   SmallVector<BasicBlock *, 8> OrigInnerBBs(NewOuter->blocks());
 
   // Add BBs from the original outer loop to the original inner loop (excluding
   // BBs already in inner loop)
   for (BasicBlock *BB : NewInner->blocks())
     if (LI->getLoopFor(BB) == NewInner)
       NewOuter->addBlockEntry(BB);
 
   // Now remove inner loop header and latch from the new inner loop and move
   // other BBs (the loop body) to the new inner loop.
   BasicBlock *OuterHeader = NewOuter->getHeader();
   BasicBlock *OuterLatch = NewOuter->getLoopLatch();
   for (BasicBlock *BB : OrigInnerBBs) {
     // Nothing will change for BBs in child loops.
     if (LI->getLoopFor(BB) != NewOuter)
       continue;
     // Remove the new outer loop header and latch from the new inner loop.
     if (BB == OuterHeader || BB == OuterLatch)
       NewInner->removeBlockFromLoop(BB);
     else
       LI->changeLoopFor(BB, NewInner);
   }
 
   // The preheader of the original outer loop becomes part of the new
   // outer loop.
   NewOuter->addBlockEntry(OrigOuterPreHeader);
   LI->changeLoopFor(OrigOuterPreHeader, NewOuter);
 
   // Tell SE that we move the loops around.
   SE->forgetLoop(NewOuter);
   SE->forgetLoop(NewInner);
 }
 
 bool LoopInterchangeTransform::transform() {
   bool Transformed = false;
   Instruction *InnerIndexVar;
 
   if (InnerLoop->getSubLoops().empty()) {
     BasicBlock *InnerLoopPreHeader = InnerLoop->getLoopPreheader();
     LLVM_DEBUG(dbgs() << "Splitting the inner loop latch\n");
     PHINode *InductionPHI = getInductionVariable(InnerLoop, SE);
     if (!InductionPHI) {
       LLVM_DEBUG(dbgs() << "Failed to find the point to split loop latch \n");
       return false;
     }
 
     if (InductionPHI->getIncomingBlock(0) == InnerLoopPreHeader)
       InnerIndexVar = dyn_cast<Instruction>(InductionPHI->getIncomingValue(1));
     else
       InnerIndexVar = dyn_cast<Instruction>(InductionPHI->getIncomingValue(0));
 
     // Ensure that InductionPHI is the first Phi node.
     if (&InductionPHI->getParent()->front() != InductionPHI)
       InductionPHI->moveBefore(&InductionPHI->getParent()->front());
 
     // Create a new latch block for the inner loop. We split at the
     // current latch's terminator and then move the condition and all
     // operands that are not either loop-invariant or the induction PHI into the
     // new latch block.
     BasicBlock *NewLatch =
         SplitBlock(InnerLoop->getLoopLatch(),
                    InnerLoop->getLoopLatch()->getTerminator(), DT, LI);
 
     SmallSetVector<Instruction *, 4> WorkList;
     unsigned i = 0;
     auto MoveInstructions = [&i, &WorkList, this, InductionPHI, NewLatch]() {
       for (; i < WorkList.size(); i++) {
         // Duplicate instruction and move it the new latch. Update uses that
         // have been moved.
         Instruction *NewI = WorkList[i]->clone();
         NewI->insertBefore(NewLatch->getFirstNonPHI());
         assert(!NewI->mayHaveSideEffects() &&
                "Moving instructions with side-effects may change behavior of "
                "the loop nest!");
         for (auto UI = WorkList[i]->use_begin(), UE = WorkList[i]->use_end();
              UI != UE;) {
           Use &U = *UI++;
           Instruction *UserI = cast<Instruction>(U.getUser());
           if (!InnerLoop->contains(UserI->getParent()) ||
               UserI->getParent() == NewLatch || UserI == InductionPHI)
             U.set(NewI);
         }
         // Add operands of moved instruction to the worklist, except if they are
         // outside the inner loop or are the induction PHI.
         for (Value *Op : WorkList[i]->operands()) {
           Instruction *OpI = dyn_cast<Instruction>(Op);
           if (!OpI ||
               this->LI->getLoopFor(OpI->getParent()) != this->InnerLoop ||
               OpI == InductionPHI)
             continue;
           WorkList.insert(OpI);
         }
       }
     };
 
     // FIXME: Should we interchange when we have a constant condition?
     Instruction *CondI = dyn_cast<Instruction>(
         cast<BranchInst>(InnerLoop->getLoopLatch()->getTerminator())
             ->getCondition());
     if (CondI)
       WorkList.insert(CondI);
     MoveInstructions();
     WorkList.insert(cast<Instruction>(InnerIndexVar));
     MoveInstructions();
 
     // Splits the inner loops phi nodes out into a separate basic block.
     BasicBlock *InnerLoopHeader = InnerLoop->getHeader();
     SplitBlock(InnerLoopHeader, InnerLoopHeader->getFirstNonPHI(), DT, LI);
     LLVM_DEBUG(dbgs() << "splitting InnerLoopHeader done\n");
   }
 
   Transformed |= adjustLoopLinks();
   if (!Transformed) {
     LLVM_DEBUG(dbgs() << "adjustLoopLinks failed\n");
     return false;
   }
 
   return true;
 }
 
 /// \brief Move all instructions except the terminator from FromBB right before
 /// InsertBefore
 static void moveBBContents(BasicBlock *FromBB, Instruction *InsertBefore) {
   auto &ToList = InsertBefore->getParent()->getInstList();
   auto &FromList = FromBB->getInstList();
 
   ToList.splice(InsertBefore->getIterator(), FromList, FromList.begin(),
                 FromBB->getTerminator()->getIterator());
 }
 
 /// Update BI to jump to NewBB instead of OldBB. Records updates to
 /// the dominator tree in DTUpdates, if DT should be preserved.
 static void updateSuccessor(BranchInst *BI, BasicBlock *OldBB,
                             BasicBlock *NewBB,
                             std::vector<DominatorTree::UpdateType> &DTUpdates) {
   assert(llvm::count_if(successors(BI),
                         [OldBB](BasicBlock *BB) { return BB == OldBB; }) < 2 &&
          "BI must jump to OldBB at most once.");
   for (unsigned i = 0, e = BI->getNumSuccessors(); i < e; ++i) {
     if (BI->getSuccessor(i) == OldBB) {
       BI->setSuccessor(i, NewBB);
 
       DTUpdates.push_back(
           {DominatorTree::UpdateKind::Insert, BI->getParent(), NewBB});
       DTUpdates.push_back(
           {DominatorTree::UpdateKind::Delete, BI->getParent(), OldBB});
       break;
     }
   }
 }
 
 // Move Lcssa PHIs to the right place.
 static void moveLCSSAPhis(BasicBlock *InnerExit, BasicBlock *InnerHeader,
                           BasicBlock *InnerLatch, BasicBlock *OuterHeader,
                           BasicBlock *OuterLatch, BasicBlock *OuterExit) {
 
   // Deal with LCSSA PHI nodes in the exit block of the inner loop, that are
   // defined either in the header or latch. Those blocks will become header and
   // latch of the new outer loop, and the only possible users can PHI nodes
   // in the exit block of the loop nest or the outer loop header (reduction
   // PHIs, in that case, the incoming value must be defined in the inner loop
   // header). We can just substitute the user with the incoming value and remove
   // the PHI.
   for (PHINode &P : make_early_inc_range(InnerExit->phis())) {
     assert(P.getNumIncomingValues() == 1 &&
            "Only loops with a single exit are supported!");
 
     // Incoming values are guaranteed be instructions currently.
     auto IncI = cast<Instruction>(P.getIncomingValueForBlock(InnerLatch));
     // Skip phis with incoming values from the inner loop body, excluding the
     // header and latch.
     if (IncI->getParent() != InnerLatch && IncI->getParent() != InnerHeader)
       continue;
 
     assert(all_of(P.users(),
                   [OuterHeader, OuterExit, IncI, InnerHeader](User *U) {
                     return (cast<PHINode>(U)->getParent() == OuterHeader &&
                             IncI->getParent() == InnerHeader) ||
                            cast<PHINode>(U)->getParent() == OuterExit;
                   }) &&
            "Can only replace phis iff the uses are in the loop nest exit or "
            "the incoming value is defined in the inner header (it will "
            "dominate all loop blocks after interchanging)");
     P.replaceAllUsesWith(IncI);
     P.eraseFromParent();
   }
 
   SmallVector<PHINode *, 8> LcssaInnerExit;
   for (PHINode &P : InnerExit->phis())
     LcssaInnerExit.push_back(&P);
 
   SmallVector<PHINode *, 8> LcssaInnerLatch;
   for (PHINode &P : InnerLatch->phis())
     LcssaInnerLatch.push_back(&P);
 
   // Lcssa PHIs for values used outside the inner loop are in InnerExit.
   // If a PHI node has users outside of InnerExit, it has a use outside the
   // interchanged loop and we have to preserve it. We move these to
   // InnerLatch, which will become the new exit block for the innermost
   // loop after interchanging.
   for (PHINode *P : LcssaInnerExit)
     P->moveBefore(InnerLatch->getFirstNonPHI());
 
   // If the inner loop latch contains LCSSA PHIs, those come from a child loop
   // and we have to move them to the new inner latch.
   for (PHINode *P : LcssaInnerLatch)
     P->moveBefore(InnerExit->getFirstNonPHI());
 
   // Deal with LCSSA PHI nodes in the loop nest exit block. For PHIs that have
   // incoming values from the outer latch or header, we have to add a new PHI
   // in the inner loop latch, which became the exit block of the outer loop,
   // after interchanging.
   if (OuterExit) {
     for (PHINode &P : OuterExit->phis()) {
       if (P.getNumIncomingValues() != 1)
         continue;
       // Skip Phis with incoming values not defined in the outer loop's header
       // and latch. Also skip incoming phis defined in the latch. Those should
       // already have been updated.
       auto I = dyn_cast<Instruction>(P.getIncomingValue(0));
       if (!I || ((I->getParent() != OuterLatch || isa<PHINode>(I)) &&
                  I->getParent() != OuterHeader))
         continue;
 
       PHINode *NewPhi = dyn_cast<PHINode>(P.clone());
       NewPhi->setIncomingValue(0, P.getIncomingValue(0));
       NewPhi->setIncomingBlock(0, OuterLatch);
       NewPhi->insertBefore(InnerLatch->getFirstNonPHI());
       P.setIncomingValue(0, NewPhi);
     }
   }
 
   // Now adjust the incoming blocks for the LCSSA PHIs.
   // For PHIs moved from Inner's exit block, we need to replace Inner's latch
   // with the new latch.
   InnerLatch->replacePhiUsesWith(InnerLatch, OuterLatch);
 }
 
 bool LoopInterchangeTransform::adjustLoopBranches() {
   LLVM_DEBUG(dbgs() << "adjustLoopBranches called\n");
   std::vector<DominatorTree::UpdateType> DTUpdates;
 
   BasicBlock *OuterLoopPreHeader = OuterLoop->getLoopPreheader();
   BasicBlock *InnerLoopPreHeader = InnerLoop->getLoopPreheader();
 
   assert(OuterLoopPreHeader != OuterLoop->getHeader() &&
          InnerLoopPreHeader != InnerLoop->getHeader() && OuterLoopPreHeader &&
          InnerLoopPreHeader && "Guaranteed by loop-simplify form");
   // Ensure that both preheaders do not contain PHI nodes and have single
   // predecessors. This allows us to move them easily. We use
   // InsertPreHeaderForLoop to create an 'extra' preheader, if the existing
   // preheaders do not satisfy those conditions.
   if (isa<PHINode>(OuterLoopPreHeader->begin()) ||
       !OuterLoopPreHeader->getUniquePredecessor())
     OuterLoopPreHeader =
         InsertPreheaderForLoop(OuterLoop, DT, LI, nullptr, true);
   if (InnerLoopPreHeader == OuterLoop->getHeader())
     InnerLoopPreHeader =
         InsertPreheaderForLoop(InnerLoop, DT, LI, nullptr, true);
 
   // Adjust the loop preheader
   BasicBlock *InnerLoopHeader = InnerLoop->getHeader();
   BasicBlock *OuterLoopHeader = OuterLoop->getHeader();
   BasicBlock *InnerLoopLatch = InnerLoop->getLoopLatch();
   BasicBlock *OuterLoopLatch = OuterLoop->getLoopLatch();
   BasicBlock *OuterLoopPredecessor = OuterLoopPreHeader->getUniquePredecessor();
   BasicBlock *InnerLoopLatchPredecessor =
       InnerLoopLatch->getUniquePredecessor();
   BasicBlock *InnerLoopLatchSuccessor;
   BasicBlock *OuterLoopLatchSuccessor;
 
   BranchInst *OuterLoopLatchBI =
       dyn_cast<BranchInst>(OuterLoopLatch->getTerminator());
   BranchInst *InnerLoopLatchBI =
       dyn_cast<BranchInst>(InnerLoopLatch->getTerminator());
   BranchInst *OuterLoopHeaderBI =
       dyn_cast<BranchInst>(OuterLoopHeader->getTerminator());
   BranchInst *InnerLoopHeaderBI =
       dyn_cast<BranchInst>(InnerLoopHeader->getTerminator());
 
   if (!OuterLoopPredecessor || !InnerLoopLatchPredecessor ||
       !OuterLoopLatchBI || !InnerLoopLatchBI || !OuterLoopHeaderBI ||
       !InnerLoopHeaderBI)
     return false;
 
   BranchInst *InnerLoopLatchPredecessorBI =
       dyn_cast<BranchInst>(InnerLoopLatchPredecessor->getTerminator());
   BranchInst *OuterLoopPredecessorBI =
       dyn_cast<BranchInst>(OuterLoopPredecessor->getTerminator());
 
   if (!OuterLoopPredecessorBI || !InnerLoopLatchPredecessorBI)
     return false;
   BasicBlock *InnerLoopHeaderSuccessor = InnerLoopHeader->getUniqueSuccessor();
   if (!InnerLoopHeaderSuccessor)
     return false;
 
   // Adjust Loop Preheader and headers
   updateSuccessor(OuterLoopPredecessorBI, OuterLoopPreHeader,
                   InnerLoopPreHeader, DTUpdates);
   updateSuccessor(OuterLoopHeaderBI, OuterLoopLatch, LoopExit, DTUpdates);
   updateSuccessor(OuterLoopHeaderBI, InnerLoopPreHeader,
                   InnerLoopHeaderSuccessor, DTUpdates);
 
   // Adjust reduction PHI's now that the incoming block has changed.
   InnerLoopHeaderSuccessor->replacePhiUsesWith(InnerLoopHeader,
                                                OuterLoopHeader);
 
   updateSuccessor(InnerLoopHeaderBI, InnerLoopHeaderSuccessor,
                   OuterLoopPreHeader, DTUpdates);
 
   // -------------Adjust loop latches-----------
   if (InnerLoopLatchBI->getSuccessor(0) == InnerLoopHeader)
     InnerLoopLatchSuccessor = InnerLoopLatchBI->getSuccessor(1);
   else
     InnerLoopLatchSuccessor = InnerLoopLatchBI->getSuccessor(0);
 
   updateSuccessor(InnerLoopLatchPredecessorBI, InnerLoopLatch,
                   InnerLoopLatchSuccessor, DTUpdates);
 
 
   if (OuterLoopLatchBI->getSuccessor(0) == OuterLoopHeader)
     OuterLoopLatchSuccessor = OuterLoopLatchBI->getSuccessor(1);
   else
     OuterLoopLatchSuccessor = OuterLoopLatchBI->getSuccessor(0);
 
   updateSuccessor(InnerLoopLatchBI, InnerLoopLatchSuccessor,
                   OuterLoopLatchSuccessor, DTUpdates);
   updateSuccessor(OuterLoopLatchBI, OuterLoopLatchSuccessor, InnerLoopLatch,
                   DTUpdates);
 
   DT->applyUpdates(DTUpdates);
   restructureLoops(OuterLoop, InnerLoop, InnerLoopPreHeader,
                    OuterLoopPreHeader);
 
   moveLCSSAPhis(InnerLoopLatchSuccessor, InnerLoopHeader, InnerLoopLatch,
                 OuterLoopHeader, OuterLoopLatch, InnerLoop->getExitBlock());
   // For PHIs in the exit block of the outer loop, outer's latch has been
   // replaced by Inners'.
   OuterLoopLatchSuccessor->replacePhiUsesWith(OuterLoopLatch, InnerLoopLatch);
 
   // Now update the reduction PHIs in the inner and outer loop headers.
   SmallVector<PHINode *, 4> InnerLoopPHIs, OuterLoopPHIs;
   for (PHINode &PHI : drop_begin(InnerLoopHeader->phis(), 1))
     InnerLoopPHIs.push_back(cast<PHINode>(&PHI));
   for (PHINode &PHI : drop_begin(OuterLoopHeader->phis(), 1))
     OuterLoopPHIs.push_back(cast<PHINode>(&PHI));
 
   auto &OuterInnerReductions = LIL.getOuterInnerReductions();
   (void)OuterInnerReductions;
 
   // Now move the remaining reduction PHIs from outer to inner loop header and
   // vice versa. The PHI nodes must be part of a reduction across the inner and
   // outer loop and all the remains to do is and updating the incoming blocks.
   for (PHINode *PHI : OuterLoopPHIs) {
     PHI->moveBefore(InnerLoopHeader->getFirstNonPHI());
     assert(OuterInnerReductions.find(PHI) != OuterInnerReductions.end() &&
            "Expected a reduction PHI node");
   }
   for (PHINode *PHI : InnerLoopPHIs) {
     PHI->moveBefore(OuterLoopHeader->getFirstNonPHI());
     assert(OuterInnerReductions.find(PHI) != OuterInnerReductions.end() &&
            "Expected a reduction PHI node");
   }
 
   // Update the incoming blocks for moved PHI nodes.
   OuterLoopHeader->replacePhiUsesWith(InnerLoopPreHeader, OuterLoopPreHeader);
   OuterLoopHeader->replacePhiUsesWith(InnerLoopLatch, OuterLoopLatch);
   InnerLoopHeader->replacePhiUsesWith(OuterLoopPreHeader, InnerLoopPreHeader);
   InnerLoopHeader->replacePhiUsesWith(OuterLoopLatch, InnerLoopLatch);
 
   return true;
 }
 
 void LoopInterchangeTransform::adjustLoopPreheaders() {
   // We have interchanged the preheaders so we need to interchange the data in
   // the preheader as well.
   // This is because the content of inner preheader was previously executed
   // inside the outer loop.
   BasicBlock *OuterLoopPreHeader = OuterLoop->getLoopPreheader();
   BasicBlock *InnerLoopPreHeader = InnerLoop->getLoopPreheader();
   BasicBlock *OuterLoopHeader = OuterLoop->getHeader();
   BranchInst *InnerTermBI =
       cast<BranchInst>(InnerLoopPreHeader->getTerminator());
 
   // These instructions should now be executed inside the loop.
   // Move instruction into a new block after outer header.
   moveBBContents(InnerLoopPreHeader, OuterLoopHeader->getTerminator());
   // These instructions were not executed previously in the loop so move them to
   // the older inner loop preheader.
   moveBBContents(OuterLoopPreHeader, InnerTermBI);
 }
 
 bool LoopInterchangeTransform::adjustLoopLinks() {
   // Adjust all branches in the inner and outer loop.
   bool Changed = adjustLoopBranches();
   if (Changed)
     adjustLoopPreheaders();
   return Changed;
 } 
