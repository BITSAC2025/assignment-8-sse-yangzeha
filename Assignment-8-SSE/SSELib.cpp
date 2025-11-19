/**
 * SSELib.cpp
 * @author kisslune 
 */

#include "SSEHeader.h"
#include "Util/Options.h"

using namespace SVF;
using namespace SVFUtil;
using namespace llvm;
using namespace z3;

/// TODO: Implement your context-sensitive ICFG traversal here to traverse each program path (once for any loop) from
/// You will need to collect each path from src node to snk node and then add the path to the `paths` set by
/// calling the `collectAndTranslatePath` method, in which translatePath method is called.
/// This implementation, slightly different from Assignment-1, requires ICFGNode* as the first argument.
void SSE::reachability(const ICFGEdge* curEdge, const ICFGNode* snk) {
    /// TODO: your code starts from here
    // curEdge 的 dst 节点就是当前所在的 ICFGNode
    const ICFGNode* curNode = curEdge->getDstNode();

    // 从 fake 的起始边（src=nullptr）开始时，为这一次 DFS 初始化状态
    if (curEdge->getSrcNode() == nullptr) {
        visited.clear();
        path.clear();
        callstack.clear();
    }

    // 记录当前 (edge, callstack) 组合是否已在当前递归栈中出现过（防止循环）
    ICFGEdgeStackPair key(curEdge, callstack);
    if (visited.find(key) != visited.end()) {
        return;
    }
    visited.insert(key);

    // 除了起始 fake edge 以外，其他边都要加入 path
    if (curEdge->getSrcNode() != nullptr) {
        path.push_back(curEdge);
    }

    // 如果已经到达 sink，则收集路径并做翻译+断言检查
    if (curNode == snk) {
        collectAndTranslatePath();
    }
    else {
        // 遍历所有后继边
        for (const ICFGEdge* outEdge : curNode->getOutEdges()) {

            // IntraCFGEdge：普通 intra 边，直接继续 DFS
            if (SVFUtil::isa<IntraCFGEdge>(outEdge)) {
                reachability(outEdge, snk);
            }
            // CallCFGEdge：遇到调用边时，往 callstack 里压入 callsite
            else if (const CallCFGEdge* callEdge = SVFUtil::dyn_cast<CallCFGEdge>(outEdge)) {
                const ICFGNode* callSite = callEdge->getCallSite();
                callstack.push_back(callSite);
                reachability(callEdge, snk);
                callstack.pop_back();
            }
            // RetCFGEdge：只允许在与顶部 callsite 匹配时“返回”
            else if (const RetCFGEdge* retEdge = SVFUtil::dyn_cast<RetCFGEdge>(outEdge)) {
                const ICFGNode* callSite = retEdge->getCallSite();
                if (!callstack.empty() && callstack.back() == callSite) {
                    // 模拟返回：先从 callstack 弹出，再 DFS，再恢复
                    callstack.pop_back();
                    reachability(retEdge, snk);
                    callstack.push_back(callSite);
                }
                // 当 callstack 为空时（如顶层外部调用），允许直接通过
                else if (callstack.empty()) {
                    reachability(retEdge, snk);
                }
            }
            else {
                assert(false && "Unknown ICFGEdge type in reachability");
            }
        }
    }

    // 回溯：把当前边从 path 中弹出
    if (curEdge->getSrcNode() != nullptr) {
        path.pop_back();
    }
    // 从当前递归栈中移除 visited 标记（同一个 (edge,ctx) 在其它路径上仍然可以访问）
    visited.erase(key);
}

/// TODO: collect each path once this method is called during reachability analysis, and
/// Collect each program path from the entry to each assertion of the program. In this function,
/// you will need (1) add each path into the paths set; (2) call translatePath to convert each path into Z3 expressions.
/// Note that translatePath returns true if the path is feasible, false if the path is infeasible; (3) If a path is feasible,
/// you will need to call assertchecking to verify the assertion (which is the last ICFGNode of this path); (4) reset z3 solver.
void SSE::collectAndTranslatePath() {
    /// TODO: your code starts from here
    if (path.empty())
        return;

    // 1) 把当前 path 以字符串形式加入 paths（主要用于调试/统计）
    std::stringstream ss;
    // 尝试把第一个真实起点节点也打印出来
    const ICFGEdge* firstEdge = path.front();
    if (const ICFGNode* firstSrc = firstEdge->getSrcNode()) {
        ss << firstSrc->getId();
    } else {
        // 如果 src 为 nullptr（理论上只有 fake 起始边），那就从 dst 开始
        ss << firstEdge->getDstNode()->getId();
    }
    for (const ICFGEdge* e : path) {
        const ICFGNode* dst = e->getDstNode();
        ss << "->" << dst->getId();
    }
    paths.insert(ss.str());

    // 2) 把 path 翻译成 Z3 约束
    bool feasible = translatePath(path);

    // 3) 如果路径可行，则对最后一个节点中的断言进行检查
    if (feasible) {
        const ICFGNode* lastNode = path.back()->getDstNode();
        assertchecking(lastNode);
    }

    // 4) 每条路径结束后都要重置 solver 和 callingCtx，避免约束串台
    resetSolver();
}

/// TODO: Implement handling of function calls
void SSE::handleCall(const CallCFGEdge* calledge) {
    /// TODO: your code starts from here
    // Algorithm 17: handleCall(callEdge) in notes
    expr_vector preCtxExprs(getCtx());

    auto callPEs = calledge->getCallPEs();
    // 先在当前 context 下收集所有实参 RHS 的表达式
    for (const CallPE* callPE : callPEs) {
        expr rhs = getZ3Expr(callPE->getRHSVarID());
        preCtxExprs.push_back(rhs);
    }

    // 切换到被调函数 context（在 callingCtx 中压入 callsite）
    pushCallingCtx(calledge->getCallSite());

    // 在 callee context 下获取形参 LHS 的表达式，并与之前 caller context 下的 RHS 相等
    for (u32_t i = 0; i < callPEs.size(); ++i) {
        expr lhs = getZ3Expr(callPEs[i]->getLHSVarID());
        addToSolver(lhs == preCtxExprs[i]);
    }
}

/// TODO: Implement handling of function returns
void SSE::handleRet(const RetCFGEdge* retEdge) {
    /// TODO: your code starts from here
    // Algorithm 14: handleRet(retEdge) in notes
    expr rhs(getCtx());  // 未使用时保持一个空 expr

    if (const RetPE* retPE = retEdge->getRetPE()) {
        // 先在 callee context 下取 RHS（返回值）
        rhs = getZ3Expr(retPE->getRHSVarID());
    }

    // 返回到 caller：弹出 callingCtx 顶部的 callsite
    popCallingCtx();

    if (const RetPE* retPE = retEdge->getRetPE()) {
        // 现在在 caller context 下获取 LHS（接收返回值的变量）
        expr lhs = getZ3Expr(retPE->getLHSVarID());
        addToSolver(lhs == rhs);
    }
}

/// TODO: Implement handling of branch statements inside a function
/// Return true if the path is feasible, false otherwise.
/// A given if/else branch on the ICFG looks like the following:
///       	     ICFGNode1 (condition %cmp)
///       	     1	/    \  0
///       	  ICFGNode2   ICFGNode3
/// edge->getCondition() returns the branch condition variable (%cmp) of type SVFValue* (for if/else) or a numeric condition variable (for switch).
/// Given the condition variable, you could obtain the SVFVar ID via "edge->getCondition()->getId()"
/// edge->getCondition() returns nullptr if this IntraCFGEdge is not a branch.
/// edge->getSuccessorCondValue() returns the actual condition value (1/0 for if/else) when this branch/IntraCFGEdge is executed. For example, the successorCondValue is 1 on the edge from ICFGNode1 to ICFGNode2, and 0 on the edge from ICFGNode1 to ICFGNode3
bool SSE::handleBranch(const IntraCFGEdge* edge) {
    /// TODO: your code starts from here
    // 已经在 handleIntra 里保证了 edge->getCondition() 非空
    const SVFValue* condVal = edge->getCondition();
    assert(condVal && "Branch edge without condition?");

    expr cond = getZ3Expr(condVal->getId());
    int succVal = static_cast<int>(edge->getSuccessorCondValue());
    expr succ = getCtx().int_val(succVal);

    // 先试探性加入 cond == succ，看该分支是否可行
    getSolver().push();
    addToSolver(cond == succ);
    if (getSolver().check() == z3::unsat) {
        // 不可行，回滚并返回 false
        getSolver().pop();
        return false;
    }
    // 可行，回滚临时状态再正式加入约束
    getSolver().pop();
    addToSolver(cond == succ);
    return true;
}

/// TODO: Translate AddrStmt, CopyStmt, LoadStmt, StoreStmt, GepStmt and CmpStmt
/// Translate AddrStmt, CopyStmt, LoadStmt, StoreStmt, GepStmt, BinaryOPStmt, CmpStmt, SelectStmt, and PhiStmt
bool SSE::handleNonBranch(const IntraCFGEdge* edge) {
    const ICFGNode* dstNode = edge->getDstNode();
    const ICFGNode* srcNode = edge->getSrcNode();
    DBOP(if(!SVFUtil::isa<CallICFGNode>(dstNode) && !SVFUtil::isa<RetICFGNode>(dstNode)) std::cout << "\n## Analyzing "<< dstNode->toString() << "\n");

    for (const SVFStmt *stmt : dstNode->getSVFStmts())
    {
        if (const AddrStmt *addr = SVFUtil::dyn_cast<AddrStmt>(stmt))
        {
            // TODO: implement AddrStmt handler here
            // p = &obj
            expr lhs = getZ3Expr(addr->getLHSVarID());
            expr rhs = getMemObjAddress(addr->getRHSVarID());
            addToSolver(lhs == rhs);
        }
        else if (const CopyStmt *copy = SVFUtil::dyn_cast<CopyStmt>(stmt))
        {
            // TODO: implement CopyStmt handler here
            // x = y
            expr lhs = getZ3Expr(copy->getLHSVarID());
            expr rhs = getZ3Expr(copy->getRHSVarID());
            addToSolver(lhs == rhs);
        }
        else if (const LoadStmt *load = SVFUtil::dyn_cast<LoadStmt>(stmt))
        {
            // TODO: implement LoadStmt handler here
            // x = *p
            expr lhs = getZ3Expr(load->getLHSVarID());
            expr rhsPtr = getZ3Expr(load->getRHSVarID());
            expr loaded = z3Mgr->loadValue(rhsPtr);
            addToSolver(lhs == loaded);
        }
        else if (const StoreStmt *store = SVFUtil::dyn_cast<StoreStmt>(stmt))
        {
            // TODO: implement StoreStmt handler here
            // *p = v
            expr lhsPtr = getZ3Expr(store->getLHSVarID());
            expr rhsVal = getZ3Expr(store->getRHSVarID());
            z3Mgr->storeValue(lhsPtr, rhsVal);
        }
        else if (const GepStmt *gep = SVFUtil::dyn_cast<GepStmt>(stmt))
        {
            // TODO: implement GepStmt handler here
            // res = gep basePtr, offset
            expr lhs = getZ3Expr(gep->getLHSVarID());
            expr basePtr = getZ3Expr(gep->getRHSVarID());

            s32_t offset = z3Mgr->getGepOffset(gep, callingCtx);
            expr gepAddr = z3Mgr->getGepObjAddress(basePtr, offset);

            addToSolver(lhs == gepAddr);
        }
            /// Given a CmpStmt "r = a > b"
            /// cmp->getOpVarID(0)/cmp->getOpVarID(1) returns the first/second operand, i.e., "a" and "b"
            /// cmp->getResID() returns the result operand "r" and cmp->getPredicate() gives you the predicate ">"
            /// Find the comparison predicates in "class CmpStmt:Predicate" under SVF/svf/include/SVFIR/SVFStatements.h
            /// You are only required to handle integer predicates, including ICMP_EQ, ICMP_NE, ICMP_UGT, ICMP_UGE, ICMP_ULT, ICMP_ULE, ICMP_SGT, ICMP_SGE, ICMP_SLE, ICMP_SLT
            /// We assume integer-overflow-free in this assignment
        else if (const CmpStmt *cmp = SVFUtil::dyn_cast<CmpStmt>(stmt))
        {
            // TODO: implement CmpStmt handler here
            expr op0 = getZ3Expr(cmp->getOpVarID(0));
            expr op1 = getZ3Expr(cmp->getOpVarID(1));
            expr res = getZ3Expr(cmp->getResID());
            expr one = getCtx().int_val(1);
            expr zero = getCtx().int_val(0);

            switch (cmp->getPredicate()) {
                case CmpStmt::ICMP_EQ:
                    addToSolver(res == ite(op0 == op1, one, zero));
                    break;
                case CmpStmt::ICMP_NE:
                    addToSolver(res == ite(op0 != op1, one, zero));
                    break;
                case CmpStmt::ICMP_UGT:
                case CmpStmt::ICMP_SGT:
                    addToSolver(res == ite(op0 > op1, one, zero));
                    break;
                case CmpStmt::ICMP_UGE:
                case CmpStmt::ICMP_SGE:
                    addToSolver(res == ite(op0 >= op1, one, zero));
                    break;
                case CmpStmt::ICMP_ULT:
                case CmpStmt::ICMP_SLT:
                    addToSolver(res == ite(op0 < op1, one, zero));
                    break;
                case CmpStmt::ICMP_ULE:
                case CmpStmt::ICMP_SLE:
                    addToSolver(res == ite(op0 <= op1, one, zero));
                    break;
                default:
                    assert(false && "Unhandled integer Cmp predicate");
            }
        }
        else if (const BinaryOPStmt *binary = SVFUtil::dyn_cast<BinaryOPStmt>(stmt))
        {
            expr op0 = getZ3Expr(binary->getOpVarID(0));
            expr op1 = getZ3Expr(binary->getOpVarID(1));
            expr res = getZ3Expr(binary->getResID());
            switch (binary->getOpcode())
            {
                case BinaryOperator::Add:
                    addToSolver(res == op0 + op1);
                    break;
                case BinaryOperator::Sub:
                    addToSolver(res == op0 - op1);
                    break;
                case BinaryOperator::Mul:
                    addToSolver(res == op0 * op1);
                    break;
                case BinaryOperator::SDiv:
                    addToSolver(res == op0 / op1);
                    break;
                case BinaryOperator::SRem:
                    addToSolver(res == op0 % op1);
                    break;
                case BinaryOperator::Xor:
                    addToSolver(res == bv2int(int2bv(32, op0) ^ int2bv(32, op1), 1));
                    break;
                case BinaryOperator::And:
                    addToSolver(res == bv2int(int2bv(32, op0) & int2bv(32, op1), 1));
                    break;
                case BinaryOperator::Or:
                    addToSolver(res == bv2int(int2bv(32, op0) | int2bv(32, op1), 1));
                    break;
                case BinaryOperator::AShr:
                    addToSolver(res == bv2int(ashr(int2bv(32, op0), int2bv(32, op1)), 1));
                    break;
                case BinaryOperator::Shl:
                    addToSolver(res == bv2int(shl(int2bv(32, op0), int2bv(32, op1)), 1));
                    break;
                default:
                    assert(false && "implement this part");
            }
        }
        else if (const BranchStmt *br = SVFUtil::dyn_cast<BranchStmt>(stmt))
        {
            DBOP(std::cout << "\t skip handled when traversal Conditional IntraCFGEdge \n");
        }
        else if (const SelectStmt *select = SVFUtil::dyn_cast<SelectStmt>(stmt)) {
            expr res = getZ3Expr(select->getResID());
            expr tval = getZ3Expr(select->getTrueValue()->getId());
            expr fval = getZ3Expr(select->getFalseValue()->getId());
            expr cond = getZ3Expr(select->getCondition()->getId());
            addToSolver(res == ite(cond == getCtx().int_val(1), tval, fval));
        }
        else if (const PhiStmt *phi = SVFUtil::dyn_cast<PhiStmt>(stmt)) {
            expr res = getZ3Expr(phi->getResID());
            bool opINodeFound = false;
            for(u32_t i = 0; i < phi->getOpVarNum(); i++){
                assert(srcNode && "we don't have a predecessor ICFGNode?");
                if (srcNode->getFun()->postDominate(srcNode->getBB(),phi->getOpICFGNode(i)->getBB()))
                {
                    expr ope = getZ3Expr(phi->getOpVar(i)->getId());
                    addToSolver(res == ope);
                    opINodeFound = true;
                }
            }
            assert(opINodeFound && "predecessor ICFGNode of this PhiStmt not found?");
        }
    }

    return true;
}

/// Traverse each program path
bool SSE::translatePath(std::vector<const ICFGEdge*>& path) {
    for (const ICFGEdge* edge : path) {
        if (const IntraCFGEdge* intraEdge = SVFUtil::dyn_cast<IntraCFGEdge>(edge)) {
            if (handleIntra(intraEdge) == false)
                return false;
        }
        else if (const CallCFGEdge* call = SVFUtil::dyn_cast<CallCFGEdge>(edge)) {
            handleCall(call);
        }
        else if (const RetCFGEdge* ret = SVFUtil::dyn_cast<RetCFGEdge>(edge)) {
            handleRet(ret);
        }
        else
            assert(false && "what other edges we have?");
    }

    return true;
}

/// Program entry
void SSE::analyse() {
    for (const ICFGNode* src : identifySources()) {
        assert(SVFUtil::isa<GlobalICFGNode>(src) && "reachability should start with GlobalICFGNode!");
        for (const ICFGNode* sink : identifySinks()) {
            const IntraCFGEdge startEdge(nullptr, const_cast<ICFGNode*>(src));
            /// start traversing from the entry to each assertion and translate each path
            reachability(&startEdge, sink);
            resetSolver();
        }
    }
}