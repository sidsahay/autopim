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

#include "llvm/Analysis/ScalarEvolution.h"

#include <vector>
#include <set>
#include <map>

using namespace llvm;

namespace {
    struct AccessPattern {
        Value* first_idx;
        Value* second_idx;
        AccessPattern(Value* v1, Value* v2) : first_idx(v1), second_idx(v2) {}
        AccessPattern() : first_idx(nullptr), second_idx(nullptr) {}
    };

    enum ASTType {
        AST_TYPE_CONSTANT,
        AST_TYPE_ARRAY,
        AST_TYPE_OP
    };

    struct ExtractAST {
        ExtractAST* left;
        ExtractAST* right;
        ASTType ast_type; 
        Value* value;
        ExtractAST(ASTType type, Value* value) : ast_type(type), value(value), left(nullptr), right(nullptr) {}
    };

    class PIMGenerator : public LoopPass {
        public:
            static char ID;
            PIMGenerator() : LoopPass(ID) {}

            Value* getIndexVariable(GetElementPtrInst* gep) {
                return gep->getOperand(gep->getNumOperands() - 1);
            }

            ExtractAST* extractComputation(Value* value, const AccessPattern& pattern) {
                //recursively carry out the extraction process till one hits either a load that is pointed to by a an
                //appropriately indexed getelementptr, or a constant value. Along the way the instructions can only
                //be add/sub/mul/div/bitwise (for now)

                if (auto constant = dyn_cast<Constant>(value)) {
                    auto ast = new ExtractAST(AST_TYPE_CONSTANT, value);
                    return ast;
                }
                else if (auto instruction = dyn_cast<Instruction>(value)) {
                    switch (instruction->getOpcode()) {
                        case Instruction::Add:
                        case Instruction::Sub:
                        case Instruction::Mul: {
                            auto ast = new ExtractAST(AST_TYPE_OP, value);
                            ast->left = extractComputation(instruction->getOperand(0), pattern);
                            ast->right = extractComputation(instruction->getOperand(1), pattern);
                            return ast;
                        }

                        case Instruction::Load: {
                            auto gep = dyn_cast<GetElementPtrInst>(instruction->getOperand(0));
                            if (getIndexVariable(gep) == pattern.first_idx || getIndexVariable(gep) == pattern.second_idx) {
                                auto ast = new ExtractAST(AST_TYPE_ARRAY, value);
                                return ast;
                            }
                        }
                        default:
                            return nullptr;
                    }
                }
                return nullptr;
            }                    
            
            void compileAST(ExtractAST* ast) {
                if (ast != NULL) {
                    switch (ast->ast_type) {
                        case AST_TYPE_CONSTANT:
                            outs() << " (CONSTANT) ";
                            break;

                        case AST_TYPE_ARRAY:
                            outs() << " (ARRAY) ";
                            break;
                   
                        case AST_TYPE_OP:
                            outs() << "(OP ";
                            if (ast->left != NULL) {
                                compileAST(ast->left);
                            }
                            if (ast->right != NULL) {
                                compileAST(ast->right);
                            }
                            outs() << ")";
                            break;
                        
                        default:         
                            break;
                    }
                }
            }

                    
            bool isLoopIterationIndependent(Loop* sub_loop, const AccessPattern& pattern) {
                //for the purposes of this analysis, the only allowed memory accesses patterns are 
                //arrays accessed by canonical induction variables
                //if the loop contains a pointer access of any other kind, it is assumed to be 
                //dependent on previous runs because proving otherwise is expensive
                //TODO: Implement array dependence analysis from lecture
                for (auto block_iter = sub_loop->block_begin(); block_iter != sub_loop->block_end(); ++block_iter) {
                    auto induction_variable = sub_loop->getCanonicalInductionVariable();
                    if (induction_variable == NULL) {
                        return false;
                    }

                    for (auto& instruction : **block_iter) {
                        //handle arrays
                        if (auto gep = dyn_cast<GetElementPtrInst>(&instruction)) {
                            auto index_variable = getIndexVariable(gep);
                            if (index_variable == induction_variable || index_variable == pattern.first_idx) {
                                continue;
                            }
                            else {
                                return false;
                            }
                        }
                        //handle pointers
                        else if (auto store = dyn_cast<StoreInst>(&instruction)) {
                            auto store_address = store->getOperand(1);
                            //validity of getelementptr is taken care of by the above condition
                            if (auto gep = dyn_cast<GetElementPtrInst>(store_address)) {
                                continue;
                            }
                            else {
                                return false;
                            }
                        }
                    }
                }

                return true;
            }

            bool subLoopIsVectorLoop(Loop* sub_loop, AccessPattern& pattern) {
                auto induction_variable = sub_loop->getCanonicalInductionVariable();
                if (induction_variable == NULL) {
                    return false;
                }
                
                //try to find a store instruction that stores a vector indexed by the loop induction variable
                for (auto block_iter = sub_loop->block_begin(); block_iter != sub_loop->block_end(); ++block_iter) {
                    for (auto& instruction : **block_iter) {
                        if (auto store = dyn_cast<StoreInst>(&instruction)) {
                            //first operand to store is value, second is address to store at
                            //address should be the result of a getelementptr with the loop induction var as the index var
                            auto stored_value = store->getOperand(0);
                            auto stored_address = store->getOperand(1);
                            
                            pattern.second_idx = sub_loop->getCanonicalInductionVariable();

                            //stored value needs to be a function of out[v], A[i][v], and constants only
                            outs() << "Function for stored value has the form: ";
                            auto ast = extractComputation(stored_value, pattern);
                            compileAST(ast);
                            outs() << "\n";
 
                            if (auto gep = dyn_cast<GetElementPtrInst>(stored_address)) {
                                if (getIndexVariable(gep) == induction_variable) {
                                    outs() << "Found appropriate getelementptr: " << *gep;
                                    //since an appropriate getelementptr was found, check if the loop iteration is independent
                                    return isLoopIterationIndependent(sub_loop, pattern);
                                }
                                else {
                                    return false;
                                }
                            }
                            else {
                                return false;
                            }
                        }
                    }
                }

                return false;
            }

            virtual bool runOnLoop(Loop* loop, LPPassManager& LPM) {
                LoopInfo& loop_info = getAnalysis<LoopInfoWrapperPass>().getLoopInfo();
                ScalarEvolution& scalar_evolution = getAnalysis<ScalarEvolutionWrapperPass>().getSE();
                //run analysis only on outermost loops
                if (loop->getLoopDepth() == 1) {
                    AccessPattern pattern;
                    pattern.first_idx = loop->getCanonicalInductionVariable();
                    outs() << "Outer loop induction variable: " << pattern.first_idx->getName()  << "\n";
                    
                    const auto& sub_loops = loop->getSubLoops();

                    for (auto sub_loop : sub_loops) {
                        if (subLoopIsVectorLoop(sub_loop, pattern)) {
                            outs() << "Found valid subloop.\n";
                        }
                    }
                }
                return false;
            }

            virtual void getAnalysisUsage(AnalysisUsage& AU) const {
                AU.addRequiredID(LoopSimplifyID);
                AU.addRequired<ScalarEvolutionWrapperPass>();
                AU.addRequired<LoopInfoWrapperPass>();
            }
    };

    char PIMGenerator::ID = 0;
    RegisterPass<PIMGenerator> PIMG("pimgen", "15745 PIM Architecture Generator");
}
