package de.uka.ilkd.key.proof;

import java.util.List;

public class Stats extends Statistics {
    public Stats(int nodes, int branches, int interactiveSteps, int symbExApps, int quantifierInstantiations, int ossApps, int mergeRuleApps, int totalRuleApps, int smtSolverApps, int dependencyContractApps, int operationContractApps, int blockLoopContractApps, int loopInvApps, long autoModeTimeInMillis, long timeInMillis, float timePerStepInMillis) {
        super(nodes, branches, interactiveSteps, symbExApps, quantifierInstantiations, ossApps, mergeRuleApps, totalRuleApps, smtSolverApps, dependencyContractApps, operationContractApps, blockLoopContractApps, loopInvApps, autoModeTimeInMillis, timeInMillis, timePerStepInMillis);
    }

    public static Stats sumStatistics(List<Stats> statsList) {
        int nodes = 0, branches = 0, interactiveSteps = 0, symbExApps = 0, quantifierInstantiations = 0,
                ossApps = 0, mergeRuleApps = 0, totalRuleApps = 0, smtSolverApps = 0, dependencyContractApps = 0,
                operationContractApps = 0, blockLoopContractApps = 0, loopInvApps = 0;
        long autoModeTimeInMillis = 0, timeInMillis = 0;
        float timePerStepInMillis = 0;

        for (Stats stats : statsList) {
            nodes += stats.nodes;
            branches += stats.branches;
            interactiveSteps += stats.interactiveSteps;
            symbExApps += stats.symbExApps;
            quantifierInstantiations += stats.quantifierInstantiations;
            ossApps += stats.ossApps;
            mergeRuleApps += stats.mergeRuleApps;
            totalRuleApps += stats.totalRuleApps;
            smtSolverApps += stats.smtSolverApps;
            dependencyContractApps += stats.dependencyContractApps;
            operationContractApps += stats.operationContractApps;
            blockLoopContractApps += stats.blockLoopContractApps;
            loopInvApps += stats.loopInvApps;
            autoModeTimeInMillis += stats.autoModeTimeInMillis;
            timeInMillis += stats.timeInMillis;
            timePerStepInMillis += stats.timePerStepInMillis;
        }

        return new Stats(nodes, branches, interactiveSteps, symbExApps, quantifierInstantiations, ossApps,
                mergeRuleApps, totalRuleApps, smtSolverApps, dependencyContractApps, operationContractApps,
                blockLoopContractApps, loopInvApps, autoModeTimeInMillis, timeInMillis,
                statsList.isEmpty() ? 0 : timePerStepInMillis / statsList.size());
    }

    public static Stats subtractStatistics(Stats s1, Stats s2) {
        return new Stats(
                s1.nodes - s2.nodes,
                s1.branches - s2.branches,
                s1.interactiveSteps - s2.interactiveSteps,
                s1.symbExApps - s2.symbExApps,
                s1.quantifierInstantiations - s2.quantifierInstantiations,
                s1.ossApps - s2.ossApps,
                s1.mergeRuleApps - s2.mergeRuleApps,
                s1.totalRuleApps - s2.totalRuleApps,
                s1.smtSolverApps - s2.smtSolverApps,
                s1.dependencyContractApps - s2.dependencyContractApps,
                s1.operationContractApps - s2.operationContractApps,
                s1.blockLoopContractApps - s2.blockLoopContractApps,
                s1.loopInvApps - s2.loopInvApps,
                s1.autoModeTimeInMillis - s2.autoModeTimeInMillis,
                s1.timeInMillis - s2.timeInMillis,
                s1.timePerStepInMillis);
    }
}
