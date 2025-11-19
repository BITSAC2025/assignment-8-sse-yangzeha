/**
 * Andersen.cpp
 * @author kisslune
 */

#include "A5Header.h"

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

    // TODO: complete the following method
    andersen.runPointerAnalysis();

    andersen.dumpResult();
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

    // ===== 收集约束（对齐 SVF 3.2 接口） =====
    for (auto it = consg->begin(); it != consg->end(); ++it) {
        SVF::ConstraintNode* cn = it->second;
        NodeID nid = cn->getId();

        // Addr：in-edges（src=object, dst=pointer=当前节点）
        {
            const auto& addrIn = cn->getAddrInEdges();
            for (auto* e : addrIn) {
                NodeID x = e->getDstID();   // 通常等于 nid
                NodeID o = e->getSrcID();   // 对象/抽象地址
                pts[x].insert(o);
            }
        }

        // Copy：out-edges u -> v
        {
            const auto& cOut = cn->getCopyOutEdges();
            for (auto* e : cOut) {
                NodeID u = e->getSrcID();
                NodeID v = e->getDstID();
                copySrc[u].push_back(v);
            }
        }

        // Load：out-edges s -> w  (w = *s)
        {
            const auto& lOut = cn->getLoadOutEdges();
            for (auto* e : lOut) {
                NodeID s = e->getSrcID();
                NodeID w = e->getDstID();
                loadEdges.emplace_back(s, w);
            }
        }

        // Store：out-edges u -> p  (*p = u)
        {
            const auto& sOut = cn->getStoreOutEdges();
            for (auto* e : sOut) {
                NodeID u = e->getSrcID();
                NodeID p = e->getDstID();
                storeEdges.emplace_back(u, p);
            }
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