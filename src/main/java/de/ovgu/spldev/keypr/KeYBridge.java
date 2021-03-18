package de.ovgu.spldev.keypr;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.ExitMainAction;
import de.uka.ilkd.key.gui.notification.NotificationEventID;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.proof.Proof;
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

class KeYBridge {
    enum Mode {HEADLESS, GUI, DEBUG}

    static class OptimizationStrategy {
        @SuppressWarnings("unused")
        static OptimizationStrategy DEFAULT = new OptimizationStrategy(
                10000, 5 * 60 * 1000, StrategyProperties.NON_LIN_ARITH_NONE);
        static OptimizationStrategy DEF_OPS = new OptimizationStrategy(
                10000, 5 * 60 * 1000, StrategyProperties.NON_LIN_ARITH_DEF_OPS);

        final int maxSteps;
        final long timeout;
        final String arithmeticTreatment;

        OptimizationStrategy(int maxSteps, int timeout, String arithmeticTreatment) {
            this.maxSteps = maxSteps;
            this.timeout = timeout;
            this.arithmeticTreatment = arithmeticTreatment;
        }

        void updateStrategySettings(StrategySettings strategySettings) {
            strategySettings.setMaxSteps(maxSteps);
            strategySettings.setTimeout(timeout);
            StrategyProperties activeStrategyProperties = strategySettings.getActiveStrategyProperties();
            activeStrategyProperties.setProperty(StrategyProperties.NON_LIN_ARITH_OPTIONS_KEY, arithmeticTreatment);
            strategySettings.setActiveStrategyProperties(activeStrategyProperties);
        }
    }

    final Mode mode;
    final KeYEnvironment<?> keYEnvironment;
    MainWindow mainWindow;
    final OptimizationStrategy optimizationStrategy;

    static final ProverTaskListener bridgeProverTaskListener = new ProverTaskListener() {
        static final int STEP = 100;

        public void taskStarted(TaskStartedInfo info) {
            System.out.print(info.getMessage() + " ");
        }

        public void taskProgress(int position) {
            if (position % STEP == 0)
                System.out.print(".");
            if (position > 0 && position % (STEP * 10) == 0)
                System.out.print(" " + position + " ");
        }

        public void taskFinished(TaskFinishedInfo info) {
            if (info != null && info.getSource() instanceof ApplyStrategy) {
                System.out.println();
                System.out.println(info);
            }
        }
    };

    static void initialize() {
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

    KeYBridge(File file, Mode _mode, OptimizationStrategy optimizationStrategy) {
        mode = _mode;
        UserInterfaceControl userInterface;
        this.optimizationStrategy = optimizationStrategy;
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
            AbstractProblemLoader loader = userInterface.load(
                    null, file, null, null, null, null, false);
            InitConfig initConfig = loader.getInitConfig();
            keYEnvironment = new KeYEnvironment<>(
                    userInterface, initConfig, loader.getProof(), loader.getProofScript(), loader.getResult());
        } catch (ProblemLoaderException e) {
            throw new RuntimeException(e);
        }
    }

    static Proof proveContract(File file, Mode mode, OptimizationStrategy optimizationStrategy,
                               @SuppressWarnings("SameParameterValue") String name) {
        System.out.println("Loading " + file);
        KeYBridge keYBridge = new KeYBridge(file, mode, optimizationStrategy);
        Contract contract = keYBridge.getContract(name);
        return keYBridge.proveContract(contract);
    }

    void debugger() {
        if (mainWindow == null) return;

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

    List<Contract> getContracts() {
        ArrayList<Contract> contracts = new ArrayList<>();
        Set<KeYJavaType> keYJavaTypes = keYEnvironment.getJavaInfo().getAllKeYJavaTypes();
        for (KeYJavaType type : keYJavaTypes)
            if (!KeYTypeUtil.isLibraryClass(type)) {
                ImmutableSet<IObserverFunction> targets =
                        keYEnvironment.getSpecificationRepository().getContractTargets(type);
                for (IObserverFunction target : targets) {
                    ImmutableSet<Contract> _contracts =
                            keYEnvironment.getSpecificationRepository().getContracts(type, target);
                    for (Contract contract : _contracts)
                        contracts.add(contract);
                }
            }
        return contracts;
    }

    List<Utils.Pair<String, Contract>> getSignaturesAndContracts() {
        return getContracts().stream().map(contract -> {
            String[] parts = contract.getTarget().name().toString().split("::");
            if (parts.length != 2)
                throw new RuntimeException("invalid contract target name");
            return new Utils.Pair<>(parts[1], contract);
        }).collect(Collectors.toList());
    }

    Contract getContract(String name) {
        List<Contract> contracts = getSignaturesAndContracts().stream()
                .filter(pair -> pair.first.equals(name))
                .map(pair -> pair.second)
                .collect(Collectors.toList());
        if (contracts.size() > 1)
            throw new IllegalArgumentException("more than one contract found with name " + name);
        return contracts.stream()
                .findFirst()
                .orElseThrow(() -> new IllegalArgumentException("no contract found with name " + name));
    }

    Proof beginProof(Contract contract) {
        try {
            return keYEnvironment.createProof(contract.createProofObl(keYEnvironment.getInitConfig(), contract));
        } catch (ProofInputException e) {
            throw new RuntimeException(e);
        }
    }

    Proof beginOrContinueProof(Contract contract) {
        Proof loadedProof = keYEnvironment.getLoadedProof();
        return loadedProof != null ? loadedProof : beginProof(contract);
    }

    Proof proveContract(Contract contract) {
        Proof proof = beginOrContinueProof(contract);
        optimizationStrategy.updateStrategySettings(proof.getSettings().getStrategySettings());
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
}
