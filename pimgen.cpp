#include "llvm/IR/Function.h"
#include "llvm/Analysis/LoopPass.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/Transforms/Utils/ValueMapper.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/CFG.h"

#include "llvm/Transforms/Utils.h"
#include "llvm/Transforms/Scalar/IndVarSimplify.h"
#include "llvm/Transforms/Utils/LoopSimplify.h"

#include <vector>
#include <set>
#include <map>

using namespace llvm;

namespace {
    class PIMGenerator : public LoopPass {
        public:
            static char ID;
            PIMGenerator() : LoopPass(ID) {}

            virtual bool runOnLoop(Loop* loop, LPPassManager& LPM) {
                LoopInfo& loop_info = getAnalysis<LoopInfoWrapperPass>().getLoopInfo();
                
                PHINode* canonical_indvar = loop->getCanonicalInductionVariable();
                
                if (canonical_indvar != NULL) {
                    outs() << canonical_indvar;
                }
                 
                return false;
            }

            virtual void getAnalysisUsage(AnalysisUsage& AU) const {
                AU.addRequiredID(LoopSimplifyID);
                AU.addRequired<LoopInfoWrapperPass>();
            }
    };

    char PIMGenerator::ID = 0;
    RegisterPass<PIMGenerator> PIMG("pimgen", "15745 PIM Architecture Generator");
}
