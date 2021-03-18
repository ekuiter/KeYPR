package de.ovgu.spldev.keypr;

import de.uka.ilkd.key.proof.Proof;

import java.io.File;
import java.nio.file.Path;
import java.util.*;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.function.Function;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

public class VerificationSystem {
    Path proofRepositoryPath;

    public static class HoareTriple {
        Set<String> implementationCalls;
        Set<String> contractCalls;

        HoareTriple(Set<String> implementationCalls, Set<String> contractCalls) {
            this.implementationCalls = implementationCalls;
            this.contractCalls = contractCalls;
        }

        Set<String> implementationCalls() {
            return implementationCalls;
        }

        Set<String> contractCalls() {
            return contractCalls;
        }
    }

    public static class State {
    }

    VerificationSystem(Path proofRepositoryPath) {
        this.proofRepositoryPath = proofRepositoryPath;
        Utils.deleteDirectory(proofRepositoryPath);
        Utils.createDirectory(proofRepositoryPath);
    }

    State beginProof(Model.Method method, Set<Model.Binding> bindings) {
        return null;
    }

    State continueProof(State state, Set<Model.Binding> bindings) {
        return null;
    }

    boolean completeProof(State state) {
        return true;
    }

    static class KeY extends VerificationSystem {
        KeYBridge.Mode mode;
        KeYBridge.OptimizationStrategy optimizationStrategy;

        KeY(KeYBridge.Mode mode, KeYBridge.OptimizationStrategy optimizationStrategy, Path proofRepositoryPath) {
            super(proofRepositoryPath);
            this.mode = mode;
            this.optimizationStrategy = optimizationStrategy;
        }

        public static class HoareTriple extends VerificationSystem.HoareTriple {
            Signature signature;
            Set<Signature> signatures;
            String requires;
            String implementation;
            String ensures;
            String assignable;

            HoareTriple(Set<String> signatures,
                        Set<String> implementationCalls, Set<String> contractCalls,
                        String requires, String code, String ensures, String assignable) {
                super(implementationCalls, contractCalls);
                this.signature = new Signature(code.split("\\{", 2)[0].trim());
                this.signatures = signatures.stream().map(Signature::new).collect(Collectors.toSet());
                this.requires = requires;
                this.implementation = "{\n    " + code.split("\\{", 2)[1].trim();
                this.ensures = ensures;
                this.assignable = assignable;
            }
        }

        public class State extends VerificationSystem.State {
            Model.Method method;
            Set<Model.Binding> bindings;
            String partialProofBefore;
            String partialProofAfter;
            Boolean isClosed;

            State(Model.Method method, Set<Model.Binding> bindings, String partialProofBefore) {
                this.method = method;
                this.bindings = bindings;
                this.partialProofBefore = partialProofBefore;
                verify();
            }

            @Override
            public String toString() {
                String str = method.feature + "_" + method.name + "_" + bindings.stream()
                        .map(binding -> String.format("%s_%s_%s_%s_%s",
                                binding.source.in.feature, binding.source.in.name, binding.source.to,
                                binding.destination.feature, binding.destination.name))
                        .collect(Collectors.joining("_"));
                return str.substring(0, Math.min(str.length(), 80)) + "_" + hashCode();
            }

            File createProofContext() {
                Path proofContextPath = proofRepositoryPath.resolve(toString());
                Utils.createDirectory(proofContextPath);
                Path javaClassPath = proofContextPath.resolve("Gen.java");
                Utils.writeFile(javaClassPath, new JavaClassGenerator(this).generate());
                if (partialProofBefore != null)
                    Utils.writeFile(proofContextPath.resolve("problem.key"), partialProofBefore);
                return proofContextPath.toFile();
            }

            void writeProof(Proof proof) {
                partialProofAfter = KeYBridge.serializeProof(proof);
                isClosed = proof.closed();
                Path proofContextPath = proofRepositoryPath.resolve(toString());
                Utils.writeFile(proofContextPath.resolve("proof.key"), partialProofAfter);
                Utils.writeFile(proofContextPath.resolve("statistics.txt"),
                        (proof.closed() ? "closed" : "open") + "\n" + proof.getStatistics().toString());
            }

            void verify() {
                File proofContext = createProofContext();
                Proof proof = KeYBridge.proveContract(
                        partialProofBefore != null
                                ? proofContext.toPath().resolve("problem.key").toFile()
                                : proofContext,
                        mode, optimizationStrategy, "main");
                writeProof(proof);
            }
        }

        @Override
        State beginProof(Model.Method method, Set<Model.Binding> bindings) {
            return new State(method, new HashSet<>(bindings), null);
        }

        @Override
        State continueProof(VerificationSystem.State state, Set<Model.Binding> bindings) {
            State _state = (State) state;
            HashSet<Model.Binding> newBindings = new HashSet<>(_state.bindings);
            newBindings.addAll(bindings);
            return new State(_state.method, newBindings, _state.partialProofAfter);
        }

        @Override
        boolean completeProof(VerificationSystem.State state) {
            return ((State) state).isClosed;
        }

        public static class Signature {
            static final Pattern PATTERN = Pattern.compile("^(.*)\\s+(.*)\\((.*)\\)$");

            String type;
            String name;
            List<Utils.Pair<String, String>> parameters;

            Signature(String type, String name, List<Utils.Pair<String, String>> parameters) {
                this.type = type;
                this.name = name;
                this.parameters = parameters;
            }

            Signature(String spec) {
                Matcher matcher = PATTERN.matcher(spec.trim());
                if (!matcher.find())
                    throw new IllegalArgumentException(
                            "invalid function specification, expected <type> <name>(<parameters>)");
                type = matcher.group(1).trim();
                name = matcher.group(2).trim();
                parameters = new ArrayList<>();
                AtomicInteger paramCounter = new AtomicInteger(1);
                Arrays.stream(matcher.group(3).trim().split(","))
                        .map(String::trim)
                        .map(str -> str.split("\\s+"))
                        .forEach(_parts -> {
                            if (String.join("", _parts).isEmpty())
                                return;
                            if (_parts.length == 1) {
                                parameters.add(new Utils.Pair<>(_parts[0], "_" + paramCounter));
                                paramCounter.getAndIncrement();
                            } else if (_parts.length == 2)
                                parameters.add(new Utils.Pair<>(_parts[0], _parts[1]));
                            else
                                throw new IllegalArgumentException("invalid parameters in signature specification");
                        });
            }

            Signature copy() {
                return new Signature(type, name, new ArrayList<>(parameters));
            }

            Signature withType(String type) {
                Signature thisCopy = copy();
                thisCopy.type = type;
                return thisCopy;
            }

            Signature withName(String name) {
                Signature thisCopy = copy();
                thisCopy.name = name;
                return thisCopy;
            }

            Signature prependName(String name) {
                return withName(name + this.name);
            }

            Signature appendName(String name) {
                return withName(this.name + name);
            }

            Signature appendParameter(String type, String name) {
                Signature thisCopy = copy();
                thisCopy.parameters = new ArrayList<>(this.parameters);
                thisCopy.parameters.add(new Utils.Pair<>(type, name));
                return thisCopy;
            }

            String parametersToJavaString() {
                return parameters != null ? "(" + parameters.stream()
                        .map(entry -> entry.first + (entry.second != null ? " " + entry.second : ""))
                        .collect(Collectors.joining(", ")) + ")" : "";
            }

            String parametersToArgumentString() {
                return parameters != null ? "(" + parameters.stream()
                        .map(entry -> entry.second)
                        .collect(Collectors.joining(", ")) + ")" : "";
            }

            String toCallString() {
                return name + parametersToArgumentString();
            }

            public String toString() {
                return type + " " + name + parametersToJavaString();
            }

            @Override
            public boolean equals(Object o) {
                if (this == o) return true;
                if (o == null || getClass() != o.getClass()) return false;
                Signature signature = (Signature) o;
                return Objects.equals(type, signature.type) && Objects.equals(name, signature.name) &&
                        Objects.equals(parameters, signature.parameters);
            }

            @Override
            public int hashCode() {
                return Objects.hash(type, name, parameters);
            }
        }

        static class JavaClassGenerator {
            State state;

            JavaClassGenerator(State state) {
                this.state = state;
            }

            String generateContract(String... args) {
                if (args.length % 2 != 0)
                    throw new IllegalArgumentException("expected map of JML keywords to values");
                StringBuilder sb = new StringBuilder();
                sb.append("/*@ ");
                for (int i = 0; i < args.length; i += 2)
                    sb.append(i > 0 ? "\n  @ " : "").append(args[i]).append(" ").append(args[i + 1]);
                return sb.append(" */").toString();
            }

            Signature originalSignature(Model.Method method) {
                return ((HoareTriple) method.hoareTriple).signature.withName(method.feature + "_" + method.name + "_original");
            }

            Signature scopedSignature(Model.Method method, Signature signature) {
                return signature.prependName(method.feature + "_" + method.name + "_");
            }

            String replaceOriginal(String condition, boolean isRequires, Signature signature) {
                return condition.replace("\\original",
                        (isRequires || signature.type.equals("void") ? signature : signature.appendParameter(signature.type,
                                signature.equals(originalSignature(state.method)) ? "\\result" : "res"))
                                .appendName(isRequires ? "_requires" : "_ensures")
                                .toCallString());
            }

            String generateAbstractMethod(Model.Method callingMethod, Signature signature) {
                Signature requiresSignature =
                        scopedSignature(callingMethod, signature).withType("boolean").appendName("_requires");
                Function<String, Signature> ensuresSignature =
                        res -> scopedSignature(callingMethod,
                                signature.type.equals("void")
                                        ? signature
                                        : signature.appendParameter(signature.type, res))
                                .withType("boolean").appendName("_ensures");
                Signature assignableSignature =
                        scopedSignature(callingMethod, signature).withType("\\locset").appendName("_assignable");
                Optional<Model.Binding> binding = state.bindings.stream()
                        .filter(_binding -> _binding.source.in.equals(callingMethod) &&
                                _binding.source.to.equals(signature.name))
                        .findFirst();
                String requiresExpansion = binding
                        .map(_binding -> " { return " + replaceOriginal(
                                ((HoareTriple) _binding.destination.hoareTriple).requires,
                                true, originalSignature(_binding.destination)) + "; }")
                        .orElse(";");
                String ensuresExpansion = binding
                        .map(_binding -> " { return " + replaceOriginal(
                                ((HoareTriple) _binding.destination.hoareTriple).ensures
                                        .replace("\\result", "res"),
                                false, originalSignature(_binding.destination)) + "; }")
                        .orElse(";");
                String assignableExpansion = binding
                        .map(_binding -> " { return " +
                                ((HoareTriple) _binding.destination.hoareTriple).assignable + "; }")
                        .orElse(";");
                return String.format("%s\n%s%s%s",
                        binding.filter(_binding -> !_binding.destination.contractCalls().isEmpty())
                                .map(_binding -> generateAbstractMethod(_binding.destination,
                                        ((HoareTriple) _binding.destination.hoareTriple)
                                                .signature.withName("original")) + "\n").orElse(""),
                        generateContract(
                                "model", requiresSignature + requiresExpansion,
                                "model", ensuresSignature.apply("res") + ensuresExpansion,
                                "model", assignableSignature + assignableExpansion),
                        callingMethod.equals(state.method) ? "\n" +
                                generateContract("requires", requiresSignature.toCallString() + ";",
                                        "ensures", ensuresSignature.apply("\\result").toCallString() + ";",
                                        "assignable", assignableSignature.toCallString() + ";") : "",
                        callingMethod.equals(state.method) ? String.format("\n%s;", signature.toString()) : "");
            }

            String generate() {
                HoareTriple hoareTriple = (HoareTriple) state.method.hoareTriple;
                return String.format("class Gen {%s\n\n%s\n%s %s\n}",
                        hoareTriple.signatures.stream()
                                .map(signature -> generateAbstractMethod(state.method, signature))
                                .collect(Collectors.joining("\n")),
                        generateContract(
                                "requires", replaceOriginal(
                                        hoareTriple.requires, true, originalSignature(state.method)) + ";",
                                "ensures", replaceOriginal(
                                        hoareTriple.ensures, false, originalSignature(state.method)) + ";",
                                "assignable", hoareTriple.assignable + ";").trim(),
                        hoareTriple.signature.withName("main"),
                        hoareTriple.implementation);
            }
        }
    }
}
