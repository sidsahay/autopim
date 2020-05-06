#include "llvm/IR/Function.h"
#include "llvm/Pass.h"
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

#include <sstream>
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

    struct LoopRange {
        unsigned int start;
        unsigned int end;
        LoopRange() : start(0), end(0) {}
        LoopRange(int s, int e) : start(s), end(e) {}
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

    struct CostModel {
        unsigned int cost_add;
        unsigned int cost_sub;
        unsigned int cost_mul;
        unsigned int cost_div;
        unsigned int cost_shift;
        unsigned int cost_and;
        unsigned int cost_or;
        unsigned int cost_xor;
        unsigned int cost_load;
        unsigned int cost_constant;

        unsigned int computeCost(ExtractAST* ast) {
            if (ast != NULL) {
                Instruction* instruction = nullptr;
                unsigned int cost_op0 = 0;
                unsigned int cost_op1 = 0;

                switch (ast->ast_type) {
                    case AST_TYPE_CONSTANT:
                        return cost_constant;

                    case AST_TYPE_ARRAY:
                        return cost_load;
               
                    case AST_TYPE_OP:
                        instruction = dyn_cast<Instruction>(ast->value);
                        
                        if (ast->left != NULL) {
                            cost_op0 = computeCost(ast->left);
                        }
                        if (ast->right != NULL) {
                            cost_op1 = computeCost(ast->right);
                        }

                        switch (instruction->getOpcode()) {
                            case Instruction::Add:
                                return cost_op0 + cost_op1 + cost_add;

                            case Instruction::Sub:
                                return cost_op0 + cost_op1 + cost_sub;

                            case Instruction::SDiv:
                            case Instruction::UDiv:
                                return cost_op0 + cost_op1 + cost_div;

                            case Instruction::Mul:
                                return cost_op0 + cost_op1 + cost_mul;

                            case Instruction::And:
                                return cost_op0 + cost_op1 + cost_and;

                            case Instruction::Or:
                                return cost_op0 + cost_op1 + cost_or;

                            case Instruction::Xor:
                                return cost_op0 + cost_op1 + cost_xor;

                            case Instruction::LShr:
                            case Instruction::AShr:
                            case Instruction::Shl:  
                                return cost_op0 + cost_op1 + cost_shift;

                            default:
                                return cost_op0 + cost_op1 + 0;
                        }
                        break;
                    
                    default:         
                        return 0;
                }
            }
            return 0;
        }
    };

    class PIMGenerator : public LoopPass {
        public:
            static char ID;
            PIMGenerator() : LoopPass(ID) {}

            std::map<int, std::string> compiled_sub_loops;
 
            Value* getIndexVariable(GetElementPtrInst* gep) {
                return gep->getOperand(gep->getNumOperands() - 1);
            }

           
            ExtractAST* extractComputation(Value* value, const AccessPattern& pattern) {
                //recursively carry out the extraction process till one hits either a load that is pointed to by a an
                //appropriately indexed getelementptr, or a constant value. Along the way the instructions can only
                //be add/sub/mul/div/bitwise

                if (auto constant = dyn_cast<Constant>(value)) {
                    auto ast = new ExtractAST(AST_TYPE_CONSTANT, value);
                    return ast;
                }
                else if (auto instruction = dyn_cast<Instruction>(value)) {
                    switch (instruction->getOpcode()) {
                        case Instruction::Add:
                        case Instruction::Sub:
                        case Instruction::SDiv:
                        case Instruction::UDiv:
                        case Instruction::Mul:
                        case Instruction::And:
                        case Instruction::Or:
                        case Instruction::Xor:
                        case Instruction::LShr:
                        case Instruction::AShr:
                        case Instruction::Shl: {
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
                    Instruction* instruction = nullptr;

                    switch (ast->ast_type) {
                        case AST_TYPE_CONSTANT:
                            outs() << " (CONSTANT)";
                            break;

                        case AST_TYPE_ARRAY:
                            outs() << " (LOAD)";
                            break;
                   
                        case AST_TYPE_OP:
                            instruction = dyn_cast<Instruction>(ast->value);
                            switch (instruction->getOpcode()) {
                                case Instruction::Add:
                                    outs() << "(ADD ";
                                    break;
                                case Instruction::Sub:
                                    outs() << "(SUB ";
                                    break;

                                case Instruction::SDiv:
                                    outs() << "(SDIV ";
                                    break;

                                case Instruction::UDiv:
                                    outs() << "(UDIV ";
                                    break;

                                case Instruction::Mul:
                                    outs() << "(MUL ";
                                    break;

                                case Instruction::And:
                                    outs() << "(AND ";
                                    break;

                                case Instruction::Or:
                                    outs() << "(OR ";
                                    break;

                                case Instruction::Xor:
                                    outs() << "(XOR ";
                                    break;

                                case Instruction::LShr:
                                    outs() << "(LSHR ";
                                    break;

                                case Instruction::AShr:
                                    outs() << "(ASHR ";
                                    break;

                                case Instruction::Shl:  
                                    outs() << "(SHL ";
                                    break;

                                default:
                                    outs() << "(UNKNOWN_OP ";
                                    break;
                            }

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

            bool subLoopIsVectorLoop(Loop* sub_loop, AccessPattern& pattern, Value** store_value) {
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
                            *store_value = stored_value;
                            
                            pattern.second_idx = sub_loop->getCanonicalInductionVariable();

                            //stored value needs to be a function of out[v], A[i][v], and constants only
                            //outs() << "Function for stored value has the form: ";
                            //auto ast = extractComputation(stored_value, pattern);
                            //compileAST(ast);
                            //outs() << "\n";
 
                            if (auto gep = dyn_cast<GetElementPtrInst>(stored_address)) {
                                if (getIndexVariable(gep) == induction_variable) {
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


           //Loop interchange as defined here is valid when the set of vectors
           //is being iterated over by the outer loop and the set of element
           //accesses is being iterated over by the inner loop. For PIM, loop
           //interchange is not valid for ">" and "<" type dependencies, it
           //only works for "=" types (i.e. directly accessed by that iteration
           //and independent of it). This is because inside the subloop it is
           //effectively being vectorized, so we do not have random access ability.
           bool isLoopInterchangeValid(Loop* loop, Loop* sub_loop, AccessPattern& pattern) {
                //if loop iterations are not independent, no point doing interchange
                if (!isLoopIterationIndependent(sub_loop, pattern)) {
                    return false;
                }

                //If all stores that are being fed by a GEP that is based on the index 
                //of the outer loop, then do loop interchange
                bool do_interchange = true;
                for (auto block_iter = sub_loop->block_begin(); block_iter != sub_loop->block_end(); ++block_iter) {
                    for (auto& instruction : **block_iter) {
                        if (auto store = dyn_cast<StoreInst>(&instruction)) {
                            auto stored_address = store->getOperand(1);
                        
                            if (auto gep = dyn_cast<GetElementPtrInst>(stored_address)) {
                                if (getIndexVariable(gep) != pattern.first_idx) {
                                    do_interchange = false;
                                }
                            }
                        }
                    }
                }

                return do_interchange;
            }

            bool loop_was_interchanged = false;
 
            //does not need to actually physically transform the code 
            //since the inner loops will be deleted and replaced by
            //a vectorized form anyway, all the loop interchange
            //needs to do is flip the access pattern and record that 
            //this flip happened.
            void doLoopInterchange(Loop* loop, Loop* sub_loop, AccessPattern& pattern) {
                outs() << "[Loop Interchange] transform complete.\n"; 
                auto x = pattern.first_idx;
                pattern.first_idx = pattern.second_idx;
                pattern.second_idx = x;
                loop_was_interchanged = true;
            }

            LoopRange getLoopRange(Loop* loop) {
                auto header = loop->getHeader();
                
                Value* start = nullptr;
                Value* end = nullptr;

                bool first_phi = true;
                bool first_icmp = true;
                
                PHINode* phi = nullptr;
                ICmpInst* icmp = nullptr;
 
                for (auto block_iter = loop->block_begin(); block_iter != loop->block_end(); ++block_iter) {
                    for (auto& instruction : **block_iter) {
                        if ((phi = dyn_cast<PHINode>(&instruction)) && first_phi) {
                            start = phi->getIncomingValue(0);
                            first_phi = false;
                        }
                        else if ((icmp = dyn_cast<ICmpInst>(&instruction)) && first_icmp) {
                            end = icmp->getOperand(1);
                            first_icmp = false;
                        }
                    }
                }
                LoopRange range(cast<ConstantInt>(start)->getSExtValue(), cast<ConstantInt>(end)->getSExtValue());
                return range;
            }

            void compileSubLoop(Loop* sub_loop, int sub_loop_num,  AccessPattern& pattern) {
                outs() << "[Sub-Loop Processing Report]\n";
                outs() << "Loop interchange";

                if (isLoopInterchangeValid(sub_loop, sub_loop, pattern)) {
                    outs() << " is required.\n";
                }
                else {
                    outs() << " is not required.\n";
                }

                outs() << "PIM compile ";
                Value* value;
                if (subLoopIsVectorLoop(sub_loop, pattern, &value)) {
                    outs() << "can be done.\n";        
                    LoopRange range = getLoopRange(sub_loop);
                    
                    auto ast = extractComputation(value, pattern);

                    std::stringstream ss;
                    ss << "pim_runindex(sub_loop_fn" << sub_loop_num << ", " << range.start << ", " << range.end <<");";
                    outs() << "Compiled: " << ss.str().c_str() << "\n";
                    outs() << "define sub_loop_fn" << sub_loop_num << " = ";
                    compileAST(ast);
                    outs() << "\n";

                    compiled_sub_loops[sub_loop_num] = ss.str();
                }
                else {
                    outs() << " cannot be done.\n";
                }
            }

            virtual bool runOnLoop(Loop* loop, LPPassManager& LPM) {
                LoopInfo& loop_info = getAnalysis<LoopInfoWrapperPass>().getLoopInfo();
                ScalarEvolution& scalar_evolution = getAnalysis<ScalarEvolutionWrapperPass>().getSE();
                auto& dominator_tree = getAnalysis<DominatorTreeWrapperPass>().getDomTree();

                //run analysis only on outermost loops
                if (loop->getLoopDepth() == 1) {
                    outs() << "[Loop Processing Report] found compatible outer loop. Checking subloops...\n";
                    AccessPattern pattern;
                    pattern.first_idx = loop->getCanonicalInductionVariable();
                    
                    const auto& sub_loops = loop->getSubLoops();
                    int i = 0;

                    for (auto sub_loop : sub_loops) {
                       compileSubLoop(sub_loop, i++, pattern); 
                    }
                }
                return false;
            }

            virtual void getAnalysisUsage(AnalysisUsage& AU) const {
                AU.addRequiredID(LoopSimplifyID);
                AU.addRequired<ScalarEvolutionWrapperPass>();
                AU.addRequired<DominatorTreeWrapperPass>();
                AU.addRequired<LoopInfoWrapperPass>();
            }
    };

    char PIMGenerator::ID = 0;
    RegisterPass<PIMGenerator> PIMG("autopim", "15745 PIM Architecture Generator");
}
