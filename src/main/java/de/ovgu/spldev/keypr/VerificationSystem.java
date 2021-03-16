package de.ovgu.spldev.keypr;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.Stats;

import java.io.Closeable;
import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.*;
import java.util.stream.Collectors;

import static de.ovgu.spldev.keypr.Utils.dumpList;

public class VerificationSystem implements Closeable, Utils.Dumpable {
    private final Program.ProofRepository proofRepository;
    private final HashMap<Program.ProofDescriptor, Path> proofContexts = new HashMap<>();
    public final Map<Program.ProofDescriptor, Program.Proof> proofs = new HashMap<>();
    private final CodeGenerator codeGenerator;
    private final boolean useAbstractContracts;

    public VerificationSystem(Program.ProofRepository proofRepository, CodeGenerator codeGenerator, boolean useAbstractContracts) {
        this.proofRepository = proofRepository;
        this.codeGenerator = codeGenerator;
        this.useAbstractContracts = useAbstractContracts;
    }

    public void close() {
        String store = proofRepository.program.getSettingValue(Program.Setting.STORE_PROOF_CONTEXTS);
        if (store != null) {
            Path storePath = Paths.get(store);
            Utils.createDirectory(storePath);
            proofContexts.forEach((proofDescriptor, path) -> {
                String csv = proofDescriptor.toCsv(), code = hashCode() + "";
                Utils.moveDirectory(path, storePath.resolve(
                        csv.substring(0, Math.min(csv.length(), 80)) + "_" +
                                Utils.toHash(csv) + "_" + code.substring(0, Math.min(code.length(), 6))));
            });
        } else {
            proofContexts.forEach((proofDescriptor, path) -> Utils.deleteDirectory(path));
        }
    }

    private KeYBridge.Mode getMode() {
        String modeValue = proofRepository.program.getSettingValue(Program.Setting.MODE);
        return modeValue.equals(Program.Setting.MODE_HEADLESS)
                ? KeYBridge.Mode.HEADLESS
                : modeValue.equals(Program.Setting.MODE_GUI)
                ? KeYBridge.Mode.GUI
                : KeYBridge.Mode.DEBUG;
    }

    private KeYBridge.OptimizationStrategy getOptimizationStrategy() {
        String optimizationStrategyValue = proofRepository.program.getSettingValue(Program.Setting.OPTIMIZATION_STRATEGY);
        return optimizationStrategyValue.equals(Program.Setting.OPTIMIZATION_STRATEGY_NONE)
                ? KeYBridge.OptimizationStrategy.NONE
                : optimizationStrategyValue.equals(Program.Setting.OPTIMIZATION_STRATEGY_DEFAULT)
                ? KeYBridge.OptimizationStrategy.DEFAULT
                : KeYBridge.OptimizationStrategy.STRICT;
    }

    private Map<String, String> getStrategyProperties() {
        return proofRepository.program.getSettingValues(Program.Setting.STRATEGY_PROPERTY).stream()
                .map(settingValue -> settingValue.split("="))
                .peek(parts -> {
                    if (parts.length != 2)
                        throw new RuntimeException("invalid strategy property setting, expected <key>=<value>");
                }).collect(Collectors.toMap(parts -> parts[0].trim(), parts -> parts[1].trim()));
    }

    private Path resolveJavaClassFile(Path path, Program.Klass klass) {
        return path.resolve(klass.name + ".java");
    }

    private File generateJavaClassFile(Path path, Program.Implementation implementation, List<Program.Binding> bindings) {
        Path klassPath = resolveJavaClassFile(path, implementation.klass);
        String javaClass = codeGenerator.generateJavaClass(implementation, bindings);
        Utils.writeFile(klassPath, javaClass);
        return path.toFile();
    }

    private Utils.Pair<File, Proof> beginProof(Path path, Program.Implementation implementation) {
        return continueProof(path, implementation, new ArrayList<>(), null, !implementation.calls.isEmpty());
    }

    private Utils.Pair<File, Proof> continueProof(Path path, Program.Implementation implementation, List<Program.Binding> bindings, String serializedProof, boolean isAbstractProof) {
        File proofContext = generateJavaClassFile(path, implementation, bindings), problemFile;
        if (serializedProof != null) {
            problemFile = proofContext.toPath().resolve("problem.key").toFile();
            Utils.writeFile(problemFile, serializedProof);
        } else
            problemFile = proofContext;
        Proof proof = proofRepository.program.getSettingValue(Program.Setting.IS_DRY_RUN).equals(Program.Setting.TRUE)
                ? KeYBridge.emptyProofForContract(problemFile, getMode(), getOptimizationStrategy(), getStrategyProperties(), implementation.signature) :
                KeYBridge.proveContract(problemFile, getMode(), getOptimizationStrategy(), getStrategyProperties(), implementation.signature, isAbstractProof, useAbstractContracts);
        File proofFile = proofContext.toPath().resolve("proof.key").toFile();
        File statisticsFile = proofContext.toPath().resolve("statistics.txt").toFile();
        Utils.writeFile(proofFile, KeYBridge.serializeProof(proof));
        Utils.writeFile(statisticsFile, proof.getStatistics().toString());
        String proofStatus = proof.closed() ? "CLOSED" : "OPEN";
        return new Utils.Pair<>(proofContext, proof);
    }

    private void verify(Program.ProofDescriptor proofDescriptor, Program.VerificationState verificationState) {
//        Path path = null;
//        try {
//            path = Files.createTempDirectory("keypr_");
//        } catch (IOException e) {
//            e.printStackTrace();
//        }
//        proofContexts.put(proofDescriptor, path);
//        Program.Proof proof;
//        if (verificationState instanceof Program.BeginProof) {
//            Utils.Pair<File, Proof> pair = beginProof(path, proofDescriptor.implementation);
//            proof = new Program.Proof(KeYBridge.serializeProof(pair.second),
//                    pair.second.getStatistics(), pair.second.closed(), pair.first.getAbsolutePath());
//        } else if (verificationState instanceof Program.ContinueProof) {
//            Program.Proof oldProof = proofs.get(((Program.ContinueProof) verificationState).proofDescriptor);
//            Utils.Pair<File, Proof> pair = continueProof(path, proofDescriptor.implementation,
//                    new ArrayList<>(proofDescriptor.bindings), oldProof != null ? oldProof.serializedProof : null,
//                    !proofDescriptor.isComplete());
//            proof = new Program.Proof(KeYBridge.serializeProof(pair.second),
//                    oldProof != null
//                            ? KeYBridge.subtractStatistics(pair.second.getStatistics(), oldProof.stats)
//                            : pair.second.getStatistics(),
//                    pair.second.closed(), pair.first.getAbsolutePath());
//            proofs.put(proofDescriptor, proof);
//        } else
//            throw new RuntimeException("invalid verification state");
//        proofs.put(proofDescriptor, proof);
    }

    public void verify() {
        for (Utils.Pair<Program.ProofDescriptor, Program.VerificationState> proofMapping : proofRepository.proofMappings)
            verify(proofMapping.first, proofMapping.second);
    }

    private boolean check(Map.Entry<Program.ProofDescriptor, Program.Proof> entry) {
        return !entry.getKey().isComplete() || entry.getValue().isClosed;
    }

    public boolean check() {
        return proofs.entrySet().stream().allMatch(this::check);
    }

    public String toString() {
        return "VerificationSystem";
    }

    public String dump(int level) {
        return Utils.join(
                Utils.indentHeading(level, toString()),
                dumpList(proofs.entrySet().stream()
                        .map(e -> new Utils.Pair<>(e.getKey(), e.getValue()))
                        .collect(Collectors.toList()), level + 1));
    }

    public String dumpIncorrectProofs() {
        return Utils.join(
                dumpList(proofs.entrySet().stream()
                        .filter(entry -> !check(entry))
                        .map(e -> new Utils.Pair<>(e.getKey(), e.getValue()))
                        .collect(Collectors.toList()), 1));
    }

    public Stats sumStatistics() {
        return KeYBridge.sumStatistics(proofs.values().stream()
                .map(proof -> proof.stats).collect(Collectors.toList()));
    }
}