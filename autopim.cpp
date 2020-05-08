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

    struct CompiledSubLoop {
        unsigned int sub_loop_index;
        std::string compiled_expr;
        LoopRange range;
        bool interchanged = false;
        bool compiled = false;
        unsigned int cost = 0;
    };

    std::map<unsigned int, CompiledSubLoop> sub_loops;

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

    //area numbers taken from Verilog synthesis
    struct CostModel {
        unsigned int cost_add = 1187;
        unsigned int cost_sub = 1187;
        unsigned int cost_mul = 16066;
        unsigned int cost_div = 61252;
        unsigned int cost_shift = 0; //negligible, it's just remapping
        unsigned int cost_and = 50;
        unsigned int cost_or = 50;    
        unsigned int cost_xor = 99;   
        unsigned int cost_load = 0;  //none because DRAM hardware does this
        unsigned int cost_cmp = 173;   
        unsigned int cost_constant = 0; //none because it can be hardwired in

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

                            case Instruction::ICmp:
                                return cost_op0 + cost_op1 + cost_cmp;

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
                        case Instruction::Shl:
                        case Instruction::ICmp: {
                            auto ast = new ExtractAST(AST_TYPE_OP, value);
                            ast->left = extractComputation(instruction->getOperand(0), pattern);
                            ast->right = extractComputation(instruction->getOperand(1), pattern);
                            return ast;
                        }

                        case Instruction::ZExt:
                        case Instruction::SExt: {
                            return extractComputation(instruction->getOperand(0), pattern);
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
                                    outs() << " (ADD";
                                    break;
                                case Instruction::Sub:
                                    outs() << " (SUB";
                                    break;

                                case Instruction::SDiv:
                                    outs() << " (SDIV";
                                    break;

                                case Instruction::UDiv:
                                    outs() << " (UDIV";
                                    break;

                                case Instruction::Mul:
                                    outs() << " (MUL";
                                    break;

                                case Instruction::And:
                                    outs() << " (AND";
                                    break;

                                case Instruction::Or:
                                    outs() << " (OR";
                                    break;

                                case Instruction::Xor:
                                    outs() << " (XOR";
                                    break;

                                case Instruction::LShr:
                                    outs() << " (LSHR";
                                    break;

                                case Instruction::AShr:
                                    outs() << " (ASHR";
                                    break;

                                case Instruction::Shl:  
                                    outs() << " (SHL";
                                    break;

                                case Instruction::ICmp:
                                    outs() << " (CMP";
                                    break;

                                default:
                                    outs() << " (UNKNOWN_OP";
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
                    CompiledSubLoop csl;
                    csl.sub_loop_index = sub_loop_num;
                    csl.compiled = true;
                    csl.range = getLoopRange(sub_loop);
                    
                    auto ast = extractComputation(value, pattern);

                    std::stringstream ss;
                    ss << "pim_runindex(sub_loop_fn" << sub_loop_num << ", " << "index);";
                    outs() << "Compiled: " << ss.str().c_str() << "\n";
                    outs() << "define sub_loop_fn" << sub_loop_num << " = ";
                    compileAST(ast);
                    outs() << "\n";
                    CostModel cm;
                    csl.cost = cm.computeCost(ast);

                    outs() << "Sub-loop function area cost (approx.): " << csl.cost << "\n";

                    csl.compiled_expr = ss.str();

                    sub_loops[sub_loop_num] = csl;
                }
                else {
                    CompiledSubLoop csl;
                    csl.compiled = false;
                    sub_loops[sub_loop_num] = csl;
                    outs() << " cannot be done.\n";
                }
            }

            //check if an instruction is a memeber of a certain basic block
            bool isInstructionInBasicBlock(Instruction* instr, BasicBlock* bb) {
                for (auto& instruction : *bb) {
                    if (instr == &instruction) {
                        return true;
                    }
                }
                return false;
            }

            //erase is valid as long as there isn't something in the loop that is from
            //outside the loop, minus the array accesses
            bool isEraseSubLoopValid(Loop* loop, DominatorTree& DT) {
                auto header = loop->getHeader();
                auto exit = loop->getExitBlock();

                BasicBlock* block = nullptr;
                for (auto succ_iter = succ_begin(header); succ_iter != succ_end(header); ++succ_iter) {
                    if (*succ_iter != exit) {
                        block = *succ_iter;
                        break;
                    }
                }

                BasicBlockEdge bbe(loop->getHeader(), block);

                for (auto& instr : *block) {
                    for (int i = 0; i < instr.getNumOperands(); i++) {
                        auto& u = instr.getOperandUse(i);
                        if (isa<GetElementPtrInst>(instr) || isa<StoreInst>(instr) || isa<LoadInst>(instr)) {
                            continue;
                        }
                        
                        if (!DT.dominates(bbe, u)) {
                            return false;
                        }
                    }
                }
                
                return true;
            }
    
            //insert PIM calls in the subloop header to trigger pim computations
            //of the form pim_runindex(subloop_num, num)
            void insertSubLoopPIMCall(Loop* sub_loop, int sub_loop_num, Value* outer_iv) {
                auto header = sub_loop->getHeader();
                Function* runindex_fn = header->getParent()->getParent()->getFunction("pim_runindex");
                if (!runindex_fn) {
                    outs() << "[Error] Could not load subloop PIM runtime function.\n";
                }
                
                Value *subloop_num_v = ConstantInt::getSigned(IntegerType::get(runindex_fn->getContext(), 32), sub_loop_num);
                Value* args[2] = {subloop_num_v, outer_iv};
                
                FunctionType* ft = cast<FunctionType>(cast<PointerType>(runindex_fn->getType())->getElementType());

                if (!ft) {
                    outs() << "[Error] could not get function type.\n";
                    return;
                }
                
                CallInst::Create(ft, runindex_fn, args, "runindex", header->getFirstNonPHI());
            }

            //insert pim_initsubloop call
            void insertPIMInitCall(Loop* loop, int subloop_num, int range_start, int range_end) {
                auto header = loop->getHeader();
                Function* init_fn = header->getParent()->getParent()->getFunction("pim_initsubloop");
                if (!init_fn) {
                    outs() << "[Error] Could not load loop PIM runtime function.\n";
                }

                FunctionType* ft = cast<FunctionType>(cast<PointerType>(init_fn->getType())->getElementType());

                if (!ft) {
                    outs() << "[Error] could not get function type.\n";
                    return;
                }

                auto& context =  init_fn->getContext();

                Value *subloop_num_v = ConstantInt::getSigned(IntegerType::get(context, 32), subloop_num); 
                Value *range_start_v = ConstantInt::getSigned(IntegerType::get(context, 32), range_start); 
                Value *range_end_v = ConstantInt::getSigned(IntegerType::get(context, 32), range_end); 
                Value* args[3] = {subloop_num_v, range_start_v, range_end_v};
                
                CallInst::Create(ft, init_fn, args, "init", header->getFirstNonPHI());
            }
                
            //insert PIM calls in the loop header to init the process
            //of the form pim_initsubloop(subloop_num, range_start, range_end)                
            void insertLoopPIMCalls(Loop* loop, int sub_loop_num_max) {
                for (int i = 0; i < sub_loop_num_max; i++) {
                    if (sub_loops[i].compiled) {
                        insertPIMInitCall(loop, i, sub_loops[i].range.start, sub_loops[i].range.end);
                    }
                }
            }
  
            //take advantage of LLVM's DCE passes
            //erase the subloop by jumping straight from the header block to the exit
            //i.e. make both arms of the br instruction point to the same block
            //dead code elimination passes will clean this up automatically
            void eraseSubLoop(Loop* sub_loop) {
                auto header = sub_loop->getHeader();
                auto exit = sub_loop->getExitBlock();
            
                if (!exit) {
                    outs() << "Error while removing sub-loop: exit block not found.\n";
                    return;
                }
               
                for (auto& instruction : *header) {
                    if (auto br = dyn_cast<BranchInst>(&instruction)) {
                        br->setSuccessor(0, exit);
                        br->setSuccessor(1, exit);
                        outs() << "Branch modified successfully, sub-loop is now dead and will be removed.\n";
                    }
                }
            }


            virtual bool runOnLoop(Loop* loop, LPPassManager& LPM) {
                LoopInfo& loop_info = getAnalysis<LoopInfoWrapperPass>().getLoopInfo();
                ScalarEvolution& scalar_evolution = getAnalysis<ScalarEvolutionWrapperPass>().getSE();
                auto& dominator_tree = getAnalysis<DominatorTreeWrapperPass>().getDomTree();
                int single_loop_count = 447;
                int total_cost = 0;

                //run analysis only on outermost loops
                if (loop->getLoopDepth() == 1) {
                    outs() << "\n[Loop Processing Report] found compatible outer loop. Checking subloops...\n";
                    AccessPattern pattern;
                    pattern.first_idx = loop->getCanonicalInductionVariable();
                    
                    const auto& sub_loop_vector = loop->getSubLoops();
                    int i = 0;
                    
                    if (sub_loop_vector.size() == 0) {
                        outs() << "Found no subloops. Attempting to process main loop itself...\n";
                        Value* value;
                        if (subLoopIsVectorLoop(loop, pattern, &value)) {
                            outs() << "can be done.\n";        
                            LoopRange range = getLoopRange(loop);
                            int sub_loop_num = single_loop_count++;
                            auto ast = extractComputation(value, pattern);

                            std::stringstream ss;
                            ss << "pim_runindex(sub_loop_fn" << sub_loop_num << ", " << "index);";
                            outs() << "Compiled: " << ss.str().c_str() << "\n";
                            outs() << "define sub_loop_fn" << sub_loop_num << " = ";
                            compileAST(ast);
                            outs() << "\n";
                            CostModel cm;
                            int cost = cm.computeCost(ast);
                            total_cost += cost;
                            outs() << "Loop function area cost (approx.): " << cost << "\n";
    
                            insertSubLoopPIMCall(loop, sub_loop_num, pattern.first_idx);
                            insertPIMInitCall(loop, sub_loop_num, range.start, range.end);
                            
                            if (isEraseSubLoopValid(loop, dominator_tree)) {
                                outs() << "Loop can be erased.\n";
                                eraseSubLoop(loop);
                            }
                            else {
                                outs() << "Loop cannot be erased.\n";
                            }
                            return true;
                        }
                        else {
                            outs() << " cannot be done.\n";
                            return false; 
                        }
                    }
                        
                    for (auto sub_loop : sub_loop_vector) {
                       compileSubLoop(sub_loop, i++, pattern); 
                    }

                    //remove the subloops that were compiled and replace them with
                    //stub functions that invoke PIM stuff
                    for (int idx = 0; idx < i; idx++) {
                        if (sub_loops[idx].compiled) {
                            if (isEraseSubLoopValid(sub_loop_vector[idx], dominator_tree)) {
                                outs() << "Sub-loop can be erased.\n";
                                insertSubLoopPIMCall(sub_loop_vector[idx], idx, pattern.first_idx);
                                eraseSubLoop(sub_loop_vector[idx]);
                            }
                            else {
                                outs() << "Sub-loop cannot be erased.\n";
                            }
                        }
                    }
            
                    insertLoopPIMCalls(loop, i);
                }
                return true;
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
