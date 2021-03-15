package de.ovgu.spldev.keypr.aoeu;

import de.ovgu.spldev.keypr.Signature;
import de.ovgu.spldev.keypr.Utils;
import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.control.ProofControl;
import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.ExitMainAction;
import de.uka.ilkd.key.gui.notification.NotificationEventID;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.macros.CompleteAbstractProofMacro;
import de.uka.ilkd.key.macros.ContinueAbstractProofMacro;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.Statistics;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.AbstractProblemLoader;
import de.uka.ilkd.key.proof.io.OutputStreamProofSaver;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.prover.ProverTaskListener;
import de.uka.ilkd.key.prover.TaskFinishedInfo;
import de.uka.ilkd.key.prover.TaskStartedInfo;
import de.uka.ilkd.key.prover.impl.ApplyStrategy;
import de.uka.ilkd.key.settings.PathConfig;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.settings.StrategySettings;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.util.KeYTypeUtil;
import org.key_project.util.collection.ImmutableSet;
import org.key_project.util.java.IOUtil;

import java.awt.event.WindowAdapter;
import java.awt.event.WindowEvent;
import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.IOException;
import java.util.*;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.stream.Collectors;

public class KeYBridge {
    public enum Mode {HEADLESS, GUI, DEBUG}

    public static class OptimizationStrategy {
        public static OptimizationStrategy NONE = new OptimizationStrategy(
                10000, 5 * 60 * 1000, false, false, false, false, false);
        public static OptimizationStrategy DEFAULT = new OptimizationStrategy(
                10000, 5 * 60 * 1000, true, true, false, false, false);
        public static OptimizationStrategy STRICT = new OptimizationStrategy(
                10000, 5 * 60 * 1000, true, true, true, true, true);

        private final int maxSteps;
        private final long timeout;
        private final List<String> forbiddenRuleSets = new ArrayList<>();
        private final List<String> forbiddenRules = new ArrayList<>();
        private final boolean firstOrderGoalsForbidden;

        private OptimizationStrategy(int maxSteps, int timeout, boolean cutsForbidden, boolean ifSplitsForbidden, boolean splitsForbidden, boolean simplifySelectForbidden, boolean firstOrderGoalsForbidden) {
            this.maxSteps = maxSteps;
            this.timeout = timeout;
            forbiddenRuleSets.add("expand_def");
            forbiddenRules.add("definition_axiom");
            if (cutsForbidden) {
                forbiddenRuleSets.add("cut");
                forbiddenRuleSets.add("cut_direct");
            }
            if (ifSplitsForbidden)
                forbiddenRules.add("ifthenelse_split");
            if (splitsForbidden) {
                forbiddenRuleSets.add("split");
                forbiddenRuleSets.add("split_if");
                forbiddenRuleSets.add("split_cond");
            }
            if (simplifySelectForbidden) {
                forbiddenRules.add("simplifySelectOfAnonEQ");
                forbiddenRules.add("simplifySelectOfAnon");
            }
            this.firstOrderGoalsForbidden = firstOrderGoalsForbidden;
        }

        private static void setProperty(StrategyProperties strategyProperties, String key, String value) {
            strategyProperties.setProperty(key, value);
        }

        private void updateStrategySettings(StrategySettings strategySettings, Map<String, String> strategyProperties) {
            if (strategyProperties.get(StrategyProperties.QUERY_OPTIONS_KEY) != null ||
                    strategyProperties.get(StrategyProperties.QUERYAXIOM_OPTIONS_KEY) != null)
                throw new RuntimeException("overriding query treatment options is not supported");
            strategySettings.setMaxSteps(maxSteps);
            strategySettings.setTimeout(timeout);
            StrategyProperties activeStrategyProperties = strategySettings.getActiveStrategyProperties();
            setProperty(activeStrategyProperties, StrategyProperties.QUERY_OPTIONS_KEY, StrategyProperties.QUERY_ON);
            setProperty(activeStrategyProperties, StrategyProperties.QUERYAXIOM_OPTIONS_KEY, StrategyProperties.QUERYAXIOM_OFF);
            setProperty(activeStrategyProperties, StrategyProperties.ABSTRACT_PROOF_FIRST_ORDER_GOALS_FORBIDDEN, firstOrderGoalsForbidden ? "true" : "false");
            strategyProperties.forEach((key, value) -> setProperty(activeStrategyProperties, key, value));
            String additionalForbiddenRuleSets = strategyProperties.get(StrategyProperties.ABSTRACT_PROOF_FORBIDDEN_RULE_SETS);
            String additionalForbiddenRules = strategyProperties.get(StrategyProperties.ABSTRACT_PROOF_FORBIDDEN_RULES);
            setProperty(activeStrategyProperties, StrategyProperties.ABSTRACT_PROOF_FORBIDDEN_RULE_SETS,
                    (additionalForbiddenRuleSets != null ? additionalForbiddenRuleSets + (forbiddenRuleSets.size() > 0 ? "," : "") : "") +
                            String.join(",", forbiddenRuleSets));
            setProperty(activeStrategyProperties, StrategyProperties.ABSTRACT_PROOF_FORBIDDEN_RULES,
                    (additionalForbiddenRules != null ? additionalForbiddenRules + (forbiddenRules.size() > 0 ? "," : "") : "") +
                            String.join(",", forbiddenRules));
            strategySettings.setActiveStrategyProperties(activeStrategyProperties);
        }
    }

    private static final ProverTaskListener bridgeProverTaskListener = new BridgeProverTaskListener();
    private final Mode mode;
    private final KeYEnvironment<?> keYEnvironment;
    private MainWindow mainWindow;
    private final OptimizationStrategy optimizationStrategy;
    private final Map<String, String> strategyProperties;

    static {
        ExitMainAction.exitSystem = false;
        System.setProperty(PathConfig.DISREGARD_SETTINGS_PROPERTY, "true");
        PathConfig.setKeyConfigDir(IOUtil.getHomeDirectory() + File.separator + ".keypr");
        Utils.runSilent(() -> {
            Consumer<Object> nop = x -> {
            };
            nop.accept(ProofIndependentSettings.DEFAULT_INSTANCE);
            nop.accept(ProofSettings.DEFAULT_SETTINGS);
        });
        ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings().setEnsureSourceConsistency(false);
        ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().setConfirmExit(false);
    }

    KeYBridge(File file, Mode _mode, OptimizationStrategy optimizationStrategy, Map<String, String> strategyProperties) {
        mode = _mode;
        UserInterfaceControl userInterface;
        this.optimizationStrategy = optimizationStrategy;
        this.strategyProperties = strategyProperties;
        if (mode == Mode.GUI || mode == Mode.DEBUG) {
            mainWindow = Utils.runSilentAndReturn(MainWindow::getInstance, false);
            userInterface = mainWindow.getUserInterface();
            mainWindow.getNotificationManager().removeNotificationTask(NotificationEventID.PROOF_CLOSED);
            mainWindow.setVisible(true);
        } else
            userInterface = new DefaultUserInterfaceControl(null);
        try {
            userInterface.removeProverTaskListener(bridgeProverTaskListener);
            userInterface.addProverTaskListener(bridgeProverTaskListener);
            AbstractProblemLoader loader = userInterface.load(null, file, null, null, null, null, false);
            InitConfig initConfig = loader.getInitConfig();
            keYEnvironment = new KeYEnvironment<>(userInterface, initConfig, loader.getProof(), loader.getProofScript(), loader.getResult());
        } catch (ProblemLoaderException e) {
            throw new RuntimeException(e);
        }
    }

    public static void runKey(OptimizationStrategy optimizationStrategy, Map<String, String> strategyProperties, File file) {
        ExitMainAction.exitSystem = true;
        MainWindow mainWindow = Utils.runSilentAndReturn(MainWindow::getInstance, false);
        optimizationStrategy.updateStrategySettings(ProofSettings.DEFAULT_SETTINGS.getStrategySettings(), strategyProperties);
        if (file != null)
            try {
                mainWindow.getUserInterface().load(null, file, null, null, null, null, false);
            } catch (ProblemLoaderException e) {
                e.printStackTrace();
            }
    }

    public static void runKey(File file) {
        runKey(OptimizationStrategy.DEFAULT, new HashMap<>(), file);
    }

    static Proof proveContract(File file, Mode mode, OptimizationStrategy optimizationStrategy, Map<String, String> strategyProperties, Signature.Method signature) {
        KeYBridge keYBridge = new KeYBridge(file, mode, optimizationStrategy, strategyProperties);
        Contract contract = keYBridge.getContract(signature);
        return keYBridge.proveContract(contract);
    }

    static Proof emptyProofForContract(File file, Mode mode, OptimizationStrategy optimizationStrategy, Map<String, String> strategyProperties, Signature.Method signature) {
        KeYBridge keYBridge = new KeYBridge(file, mode, optimizationStrategy, strategyProperties);
        return keYBridge.beginProof(keYBridge.getContract(signature));
    }

    private void debugger() {
        if (mainWindow == null) {
            return;
        }

        mainWindow.setVisible(true);
        Object lock = new Object();
        Thread thread = new Thread(() -> {
            synchronized (lock) {
                while (mainWindow.isVisible())
                    try {
                        lock.wait();
                    } catch (InterruptedException e) {
                        e.printStackTrace();
                    }
            }
        });
        thread.start();
        WindowAdapter windowAdapter = new WindowAdapter() {
            public void windowClosing(WindowEvent e) {
                synchronized (lock) {
                    mainWindow.setVisible(false);
                    lock.notify();
                }
            }
        };
        mainWindow.addWindowListener(windowAdapter);
        try {
            thread.join();
        } catch (InterruptedException e) {
            throw new RuntimeException(e);
        }
        mainWindow.removeWindowListener(windowAdapter);
    }

    private List<Contract> getContracts() {
        ArrayList<Contract> contracts = new ArrayList<>();
        Set<KeYJavaType> keYJavaTypes = keYEnvironment.getJavaInfo().getAllKeYJavaTypes();
        for (KeYJavaType type : keYJavaTypes)
            if (!KeYTypeUtil.isLibraryClass(type)) {
                ImmutableSet<IObserverFunction> targets = keYEnvironment.getSpecificationRepository().getContractTargets(type);
                for (IObserverFunction target : targets) {
                    ImmutableSet<Contract> _contracts = keYEnvironment.getSpecificationRepository().getContracts(type, target);
                    for (Contract contract : _contracts)
                        contracts.add(contract);
                }
            }
        return contracts;
    }

    private List<Utils.Pair<Signature.Method, Contract>> getSignaturesAndContracts() {
        Function<KeYJavaType, String> getTypeName = keYJavaType ->
                keYJavaType == KeYJavaType.VOID_TYPE ? "void" : keYJavaType.getSort().name().toString();
        return getContracts().stream().map(contract -> {
            IObserverFunction target = contract.getTarget();
            String[] parts = target.name().toString().split("::");
            if (parts.length != 2)
                throw new RuntimeException("invalid contract target name");
            if (target.getType() == null)
                return null;
            return new Utils.Pair<>(new Signature.Method(
                    getTypeName.apply(target.getType()) + " " +
                            getTypeName.apply(target.getContainerType()) + "::" +
                            parts[1] + "(" +
                            target.getParamTypes().stream()
                                    .map(getTypeName)
                                    .collect(Collectors.joining(", ")) + ")"), contract);
        }).filter(Objects::nonNull).collect(Collectors.toList());
    }

    private Contract getContract(Signature.Method signature) {
        List<Contract> contracts = getSignaturesAndContracts().stream()
                .filter(pair -> pair.first.matches(signature))
                .map(pair -> pair.second)
                .collect(Collectors.toList());
        if (contracts.size() > 1)
            throw new IllegalArgumentException("more than one contract found for signature " + signature);
        return contracts.stream()
                .findFirst()
                .orElseThrow(() -> new IllegalArgumentException("no contract found for signature " + signature));
    }

    private Proof beginProof(Contract contract) {
        try {
            return keYEnvironment.createProof(contract.createProofObl(keYEnvironment.getInitConfig(), contract));
        } catch (ProofInputException e) {
            throw new RuntimeException(e);
        }
    }

    private Proof beginOrContinueProof(Contract contract) {
        Proof loadedProof = keYEnvironment.getLoadedProof();
        return loadedProof != null ? loadedProof : beginProof(contract);
    }

    private Proof proveContract(Contract contract) {
        Proof proof = beginOrContinueProof(contract);
        optimizationStrategy.updateStrategySettings(proof.getSettings().getStrategySettings(), strategyProperties);
        keYEnvironment.getProofControl().startAndWaitForAutoMode(proof);
        if (mode == Mode.DEBUG)
            debugger();
        return proof;
    }

    static String serializeProof(Proof proof) {
        try {
            ByteArrayOutputStream outputStream = new ByteArrayOutputStream();
            new OutputStreamProofSaver(proof).save(outputStream);
            return outputStream.toString();
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    static Statistics sumStatistics(List<Statistics> statisticsList) {
        int nodes = 0, branches = 0, interactiveSteps = 0, symbExApps = 0, quantifierInstantiations = 0,
                ossApps = 0, mergeRuleApps = 0, totalRuleApps = 0, smtSolverApps = 0, dependencyContractApps = 0,
                operationContractApps = 0, blockLoopContractApps = 0, loopInvApps = 0;
        long autoModeTimeInMillis = 0, timeInMillis = 0;
        float timePerStepInMillis = 0;

        for (Statistics statistics : statisticsList) {
            nodes += statistics.nodes;
            branches += statistics.branches;
            interactiveSteps += statistics.interactiveSteps;
            symbExApps += statistics.symbExApps;
            quantifierInstantiations += statistics.quantifierInstantiations;
            ossApps += statistics.ossApps;
            mergeRuleApps += statistics.mergeRuleApps;
            totalRuleApps += statistics.totalRuleApps;
            smtSolverApps += statistics.smtSolverApps;
            dependencyContractApps += statistics.dependencyContractApps;
            operationContractApps += statistics.operationContractApps;
            blockLoopContractApps += statistics.blockLoopContractApps;
            loopInvApps += statistics.loopInvApps;
            autoModeTimeInMillis += statistics.autoModeTimeInMillis;
            timeInMillis += statistics.timeInMillis;
            timePerStepInMillis += statistics.timePerStepInMillis;
        }

        return new Statistics(nodes, branches, interactiveSteps, symbExApps, quantifierInstantiations, ossApps,
                mergeRuleApps, totalRuleApps, smtSolverApps, dependencyContractApps, operationContractApps,
                blockLoopContractApps, loopInvApps, autoModeTimeInMillis, timeInMillis,
                statisticsList.isEmpty() ? 0 : timePerStepInMillis / statisticsList.size());
    }

    static Statistics subtractStatistics(Statistics s1, Statistics s2) {
        return new Statistics(
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

    private static class BridgeProverTaskListener implements ProverTaskListener {
        private static final int STEP = 100;

        public void taskStarted(TaskStartedInfo info) {
            if (Utils.isDebugLevel())
                System.out.print(info.getMessage() + " ");
        }

        public void taskProgress(int position) {
            if (Utils.isDebugLevel() && position % STEP == 0)
                System.out.print(".");
            if (Utils.isDebugLevel() && position > 0 && position % (STEP * 10) == 0)
                System.out.print(" " + position + " ");
        }

        public void taskFinished(TaskFinishedInfo info) {
            if (info != null && Utils.isDebugLevel() && info.getSource() instanceof ApplyStrategy) {
                System.out.println();
                System.out.println(info);
            }
        }
    }
}
