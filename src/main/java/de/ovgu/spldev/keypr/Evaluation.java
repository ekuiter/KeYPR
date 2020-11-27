package de.ovgu.spldev.keypr;

import de.uka.ilkd.key.proof.Statistics;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

public class Evaluation {
    private final List<String> domain;
    private final Map<Program.ProofDescriptor, Program.Proof> proofs;

    public Evaluation(List<String> domain, Map<Program.ProofDescriptor, Program.Proof> proofs) {
        this.domain = domain;
        this.proofs = proofs;
    }

    public static Evaluation reduce(List<String> domain, List<Evaluation> evaluations) {
        Map<Program.ProofDescriptor, Program.Proof> proofs = new HashMap<>();
        for (Evaluation evaluation : evaluations)
            proofs.putAll(evaluation.proofs);
        return new Evaluation(domain, proofs);
    }

    private boolean check(Utils.Pair<Program.ProofDescriptor, Program.Proof> pair) {
        return !pair.first.isComplete() || pair.second.isClosed;
    }

    private List<Statistics> evaluate() {
        return domain.stream()
                .map(proofDescriptorString -> {
                    Program.ProofDescriptor proofDescriptor =
                            proofs.keySet().stream()
                                    .filter(_proofDescriptor -> _proofDescriptor.toCsv().equals(proofDescriptorString))
                                    .findFirst().orElse(null);
                    return proofDescriptor != null
                            ? KeYBridge.sumStatistics(proofs.keySet().stream()
                            .filter(_proofDescriptor -> _proofDescriptor.toCsv().equals(proofDescriptorString))
                            .map(_proofDescriptor -> proofs.get(_proofDescriptor).statistics)
                            .collect(Collectors.toList()))
                            : null;
                }).collect(Collectors.toList());
    }

    public String evaluateSemanticsCsv() {
        return domain.stream()
                .map(proofDescriptorString -> {
                    Program.ProofDescriptor proofDescriptor =
                            proofs.keySet().stream()
                                    .filter(_proofDescriptor -> _proofDescriptor.toCsv().equals(proofDescriptorString))
                                    .findFirst().orElse(null);
                    return proofDescriptor != null
                    ? (proofs.keySet().stream()
                            .filter(_proofDescriptor -> _proofDescriptor.toCsv().equals(proofDescriptorString))
                            .allMatch(_proofDescriptor -> check(new Utils.Pair<>(_proofDescriptor, proofs.get(proofDescriptor))))
                            ? "1" : "0")
                    : "";
                }).collect(Collectors.joining("; "));
    }

    public String evaluateNodesCsv() {
        return evaluate().stream()
                .map(statistics -> statistics != null ? statistics.nodes + "" : "")
                .collect(Collectors.joining("; "));
    }

    public String evaluateTimeCsv() {
        return evaluate().stream()
                .map(statistics -> statistics != null ? statistics.autoModeTimeInMillis + "" : "")
                .collect(Collectors.joining("; "));
    }

    public String evaluateAvgTimeCsv() {
        return evaluate().stream()
                .map(statistics -> statistics != null ? String.format("%.2f", statistics.timePerStepInMillis).replace(".", ",") : "")
                .collect(Collectors.joining("; "));
    }
}
