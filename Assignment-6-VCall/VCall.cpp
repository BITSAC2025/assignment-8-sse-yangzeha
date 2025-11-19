/**
 * Andersen.cpp
 * @author kisslune
 */

#include "A6Header.h"

using namespace llvm;
using namespace std;

int main(int argc, char** argv)
{
    auto moduleNameVec =
            OptionBase::parseOptions(argc, argv, "Whole Program Points-to Analysis",
                                     "[options] <input-bitcode...>");

    SVF::LLVMModuleSet::buildSVFModule(moduleNameVec);

    SVF::SVFIRBuilder builder;
    auto pag = builder.build();
    auto consg = new SVF::ConstraintGraph(pag);
    consg->dump();

    Andersen andersen(consg);
    auto cg = pag->getCallGraph();

    // TODO: complete the following two methods
    andersen.runPointerAnalysis();
    andersen.updateCallGraph(cg);

    cg->dump();
    SVF::LLVMModuleSet::releaseLLVMModuleSet();
	return 0;
}


void Andersen::runPointerAnalysis()
{
    // TODO: complete this method. Point-to set and worklist are defined in A5Header.h
    //  The implementation of constraint graph is provided in the SVF library

    using NodeID = unsigned;

    // 邻接缓存
    std::unordered_map<NodeID, std::vector<NodeID>> copySrc;   // u -> {v...}
    std::vector<std::pair<NodeID, NodeID>> loadEdges;          // (s, w)  w = *s
    std::vector<std::pair<NodeID, NodeID>> storeEdges;         // (u, p)  *p = u

    // ===== 收集约束（对齐 SVF 接口） =====
    for (auto it = consg->begin(); it != consg->end(); ++it) {
        SVF::ConstraintNode* cn = it->second;

        // Addr：in-edges（src=object, dst=pointer）
        for (auto* e : cn->getAddrInEdges()) {
            NodeID x = e->getDstID();
            NodeID o = e->getSrcID();
            pts[x].insert(o);
        }

        // Copy：out-edges u -> v
        for (auto* e : cn->getCopyOutEdges()) {
            NodeID u = e->getSrcID();
            NodeID v = e->getDstID();
            copySrc[u].push_back(v);
        }

        // Load：out-edges s -> w  (w = *s)
        for (auto* e : cn->getLoadOutEdges()) {
            NodeID s = e->getSrcID();
            NodeID w = e->getDstID();
            loadEdges.emplace_back(s, w);
        }

        // Store：out-edges u -> p  (*p = u)
        for (auto* e : cn->getStoreOutEdges()) {
            NodeID u = e->getSrcID();
            NodeID p = e->getDstID();
            storeEdges.emplace_back(u, p);
        }
    }

    // ===== 初始化工作队列 =====
    WorkList<NodeID> wl;

    // 把由 Addr 初始化过的节点入队
    for (auto& pr : pts) wl.push(pr.first);

    // 确保每个图节点在 pts 中都有键
    for (auto it = consg->begin(); it != consg->end(); ++it) {
        (void)pts[it->second->getId()];
    }

    // ===== 迭代求解 =====
    while (!wl.empty()) {
        NodeID n = wl.pop();
        const auto& pn_ref = pts[n]; // 只读引用

        // --- Copy：n -> v : pts[v] ∪= pts[n]
        if (auto it = copySrc.find(n); it != copySrc.end()) {
            for (NodeID v : it->second) {
                bool changed = false;
                for (auto x : pn_ref) {
                    if (pts[v].insert(x).second) changed = true;
                }
                if (changed) wl.push(v);
            }
        }

        // --- Load：处理 (s, w)
        for (const auto& sw : loadEdges) {
            NodeID s = sw.first;
            NodeID w = sw.second;
            bool pushed = false;

            // A：s == n  => ∀o∈pts[s], pts[w] ∪= pts[o]
            if (s == n) {
                for (NodeID o : pts[s]) {
                    bool changed = false;
                    for (auto x : pts[o]) {
                        if (pts[w].insert(x).second) changed = true;
                    }
                    if (changed) pushed = true;
                }
            }

            // B：n ∈ pts[s]  => pts[w] ∪= pts[n]
            if (!pushed && pts[s].count(n)) {
                bool changed = false;
                for (auto x : pn_ref) {
                    if (pts[w].insert(x).second) changed = true;
                }
                if (changed) pushed = true;
            }

            if (pushed) wl.push(w);
        }

        // --- Store：处理 (u, p)
        for (const auto& up : storeEdges) {
            NodeID u = up.first;
            NodeID p = up.second;

            // A：u == n  => ∀o∈pts[p], pts[o] ∪= pts[n]
            if (u == n) {
                for (NodeID o : pts[p]) {
                    bool changed = false;
                    for (auto x : pn_ref) {
                        if (pts[o].insert(x).second) changed = true;
                    }
                    if (changed) wl.push(o);
                }
            }

            // B：p == n  => ∀o∈pts[p], pts[o] ∪= pts[u]
            if (p == n) {
                for (NodeID o : pts[p]) {
                    bool changed = false;
                    for (auto x : pts[u]) {
                        if (pts[o].insert(x).second) changed = true;
                    }
                    if (changed) wl.push(o);
                }
            }

            // C：n ∈ pts[p] => pts[n] ∪= pts[u]
            if (pts[p].count(n)) {
                bool changed = false;
                for (auto x : pts[u]) {
                    if (pts[n].insert(x).second) changed = true;
                }
                if (changed) wl.push(n);
            }
        }
    }
}


void Andersen::updateCallGraph(SVF::CallGraph* cg)
{
    // TODO: complete this method.
    //  The implementation of call graph is provided in the SVF library

    SVF::PAG* pag = SVF::PAG::getPAG();
    if (!pag || !cg) return;

    // 遍历所有调用点（元素是 const CallICFGNode*）
    for (const SVF::CallICFGNode* callNode : pag->getCallSiteSet())
    {
        if (!callNode) continue;
        if (!callNode->isIndirectCall()) continue;  // 只处理函数指针调用

        // 调用者（函数对象）
        const SVF::FunObjVar* callerFun = callNode->getCaller();
        if (!callerFun) continue;

        // 关键：在你的版本中使用 getFun() 取得“被调实体”
        // - 若为直接调用：返回 FunObjVar（本函数中跳过）
        // - 若为间接调用：返回函数指针变量 SVFVar（我们用它的 Id 查 pts）
        const SVF::SVFVar* calleeEntity = callNode->getFun();
        if (!calleeEntity) continue;

        // 如果是直接调用（FunObjVar），本作业不需要我们在这里处理，跳过即可
        if (llvm::isa<SVF::FunObjVar>(calleeEntity))
            continue;

        // 否则 calleeEntity 是“函数指针变量” -> 用其 NodeID 查 points-to 目标
        unsigned fptrId = calleeEntity->getId();
        auto it = pts.find(fptrId);
        if (it == pts.end()) continue;

        // 遍历候选目标，将函数目标加入调用图
        for (unsigned objId : it->second)
        {
            const SVF::PAGNode* baseObj = pag->getBaseObject(objId);
            if (!baseObj) continue;

            // 需要目标是函数对象（FunObjVar）
            if (!llvm::isa<SVF::FunObjVar>(baseObj)) continue;
            const SVF::FunObjVar* calleeFun = llvm::cast<const SVF::FunObjVar>(baseObj);

            // 根据你头文件的签名：需传 (callsite, callerFun, calleeFun)
            cg->addIndirectCallGraphEdge(callNode, callerFun, calleeFun);
        }
    }

    std::cout << "[VCall] Call graph updated using Andersen points-to results.\n";
}