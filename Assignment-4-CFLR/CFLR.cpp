/**
 * CFLR.cpp
 * @author kisslune 
 */

#include "A4Header.h"

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
    pag->dump();

    CFLR solver;
    solver.buildGraph(pag);
    // TODO: complete this method
    solver.solve();
    solver.dumpResult();

    LLVMModuleSet::releaseLLVMModuleSet();
    return 0;
}


void CFLR::solve()
{
    // TODO: complete this function. The implementations of graph and worklist are provided.
    //  You need to:
    //  1. implement the grammar production rules into code;
    //  2. implement the dynamic-programming CFL-reachability algorithm.
    //  You may need to add your new methods to 'CFLRGraph' and 'CFLR'.

    // Step 1: Initialize worklist with all existing edges
    // Add all existing edges in the graph to worklist
    assert(graph && "CFLR graph not built yet.");

    // ========== Unary rules ==========
    std::vector<std::pair<EdgeLabel, EdgeLabel>> unaryRules = {
        {Copy, VF},   // Copy → VF
        {CopyBar, VFBar},   // CopyBar → VFBar
    };

    // ========== Binary rules ==========
    using Rule = std::tuple<EdgeLabel, EdgeLabel, EdgeLabel>;
    std::vector<Rule> binaryRules = {
        // PT and PTBar
        {VFBar, AddrBar, PT},
        {Addr, VF, PTBar},

        // VF rules
        {VF, VF, VF},
        {SV, Load, VF},
        {PV, Load, VF},
        {Store, VP, VF},

        // VFBar rules
        {VFBar, VFBar, VFBar},
        {LoadBar, SVBar, VFBar},
        {LoadBar, VP, VFBar},
        {PV, StoreBar, VFBar},

        // VA rules
        {LV, Load, VA},
        {VFBar, VA, VA},
        {VA, VF, VA},

        // SV rules
        {Store, VA, SV},

        // SVBar rules
        {VA, StoreBar, SVBar},

        // PV rules
        {PTBar, VA, PV},

        // VP rules
        {VA, PT, VP},
        // LV rules
        {LoadBar, VA, LV},
    };

    // ===== Initialize ε-edges =====
    // 文法中 ε 的非终结符：VF, VFBar, VA
    std::vector<EdgeLabel> epsilonLabels = {VF, VFBar, VA};
    for (auto &nodePair : graph->getSuccessorMap())
    {
        unsigned node = nodePair.first;
        for (EdgeLabel lbl : epsilonLabels)
        {
            if (!graph->hasEdge(node, node, lbl))
            {
                graph->addEdge(node, node, lbl);
                workList.push(CFLREdge(node, node, lbl));
            }
        }
    }


    // Build index maps for efficiency
    std::unordered_map<EdgeLabel, std::vector<std::pair<EdgeLabel, EdgeLabel>>> byLeft, byRight;
    for (auto &r : binaryRules)
    {
        EdgeLabel A = std::get<0>(r), B = std::get<1>(r), C = std::get<2>(r);
        byLeft[A].push_back({B, C});
        byRight[B].push_back({A, C});
    }

    // ===== Initialize the worklist with all existing edges =====
    for (auto &srcEntry : graph->getSuccessorMap())
    {
        unsigned src = srcEntry.first;
        for (auto &lblEntry : srcEntry.second)
        {
            EdgeLabel lbl = lblEntry.first;
            for (unsigned dst : lblEntry.second)
                workList.push(CFLREdge(src, dst, lbl));
        }
    }

    // ===== Dynamic programming iteration =====
    while (!workList.empty())
    {
        CFLREdge e = workList.pop();
        unsigned u = e.src, v = e.dst;
        EdgeLabel L = e.label;

        // ---- Unary rules ----
        for (auto &ur : unaryRules)
        {
            if (ur.first == L)
            {
                EdgeLabel Lp = ur.second;
                if (!graph->hasEdge(u, v, Lp))
                {
                    graph->addEdge(u, v, Lp);
                    workList.push(CFLREdge(u, v, Lp));
                }
            }
        }

        auto &succMap = graph->getSuccessorMap();
        auto &predMap = graph->getPredecessorMap();

        // ---- Binary join: (L ; B) -> C ----
        if (byLeft.count(L))
        {
            for (auto &pairBC : byLeft[L])
            {
                EdgeLabel B = pairBC.first, C = pairBC.second;
                auto succIt = succMap.find(v);
                if (succIt != succMap.end())
                {
                    auto lblIt = succIt->second.find(B);
                    if (lblIt != succIt->second.end())
                    {
                        for (unsigned w : lblIt->second)
                        {
                            if (!graph->hasEdge(u, w, C))
                            {
                                graph->addEdge(u, w, C);
                                workList.push(CFLREdge(u, w, C));
                            }
                        }
                    }
                }
            }
        }

        // ---- Binary join: (A ; L) -> C ----
        if (byRight.count(L))
        {
            for (auto &pairAC : byRight[L])
            {
                EdgeLabel A = pairAC.first, C = pairAC.second;
                auto predIt = predMap.find(u);
                if (predIt != predMap.end())
                {
                    auto lblIt = predIt->second.find(A);
                    if (lblIt != predIt->second.end())
                    {
                        for (unsigned p : lblIt->second)
                        {
                            if (!graph->hasEdge(p, v, C))
                            {
                                graph->addEdge(p, v, C);
                                workList.push(CFLREdge(p, v, C));
                            }
                        }
                    }
                }
            }
        }
    }
}
