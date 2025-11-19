/**
 * ICFG.cpp
 * @author kisslune 
 */

#include "CFGA.h"

using namespace SVF;
using namespace llvm;
using namespace std;

int main(int argc, char **argv)
{
    auto moduleNameVec =
            OptionBase::parseOptions(argc, argv, "Whole Program Points-to Analysis",
                                     "[options] <input-bitcode...>");

    LLVMModuleSet::buildSVFModule(moduleNameVec);

    SVFIRBuilder builder;
    auto pag = builder.build();
    auto icfg = pag->getICFG();

    CFGAnalysis analyzer = CFGAnalysis(icfg);

    // TODO: complete the following method: 'CFGAnalysis::analyze'
    analyzer.analyze(icfg);

    analyzer.dumpPaths();
    LLVMModuleSet::releaseLLVMModuleSet();
    return 0;
}


void CFGAnalysis::analyze(SVF::ICFG *icfg)
{
    // Sources and sinks are specified when an analyzer is instantiated.
    for (auto src : sources)
        for (auto snk : sinks)
        {
            // TODO: DFS the graph, starting from src and detecting the paths ending at snk.
            // Use the class method 'recordPath' (already defined) to record the path you detected.
            //@{
            
            // 使用 DFS 搜索所有路径，call/return 匹配
            vector<unsigned int> path;
            unordered_set<unsigned int> visited;
            vector<unsigned int> callStack;

            function<void(unsigned int)> dfs = [&](unsigned int nodeID) {
                path.push_back(nodeID);
                visited.insert(nodeID);

                // 判断是否到达 sink
                if (nodeID == snk) {
                    recordPath(path);
                    path.pop_back();
                    visited.erase(nodeID);
                    return;
                }

                SVF::ICFGNode* node = icfg->getICFGNode(nodeID);

                // 判断 call/return 节点
                bool isCall = false, isRet = false;
                for (auto edge : node->getOutEdges()) {
                    if (SVFUtil::dyn_cast<SVF::CallCFGEdge>(edge)) {
                        isCall = true;
                        break;
                    }
                    if (SVFUtil::dyn_cast<SVF::RetCFGEdge>(edge)) {
                        isRet = true;
                        break;
                    }
                }
                if (isCall) callStack.push_back(nodeID);
                if (isRet) { if (!callStack.empty()) callStack.pop_back(); }

                // 获取后继节点
                for (auto edge : node->getOutEdges()) {
                    SVF::ICFGNode* succNode = edge->getDstNode();
                    unsigned succID = succNode->getId();
                    if (visited.find(succID) == visited.end()) {
                        dfs(succID);
                    }
                }

                // 回溯 call/return
                if (isCall) {
                    if (!callStack.empty() && callStack.back() == nodeID) callStack.pop_back();
                }

                path.pop_back();
                visited.erase(nodeID);
            };

            dfs(src);
            //@}
        }
}
