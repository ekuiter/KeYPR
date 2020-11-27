package de.ovgu.spldev.keypr;

import de.uka.ilkd.key.proof.Statistics;
import org.pmw.tinylog.Logger;

import java.util.*;
import java.util.stream.Collectors;

import static de.ovgu.spldev.keypr.Utils.dumpList;

public class Program implements Utils.Dumpable {
    public Object clojureObject;
    public List<Setting> settings;
    public List<Macro> macros;
    public List<Klass> classes;
    public List<Binding> bindings;

    public Program(Object clojureObject, List<Setting> settings, List<Macro> macros, List<Klass> classes, List<Binding> bindings) {
        this.clojureObject = clojureObject;
        this.settings = settings;
        this.macros = macros;
        this.classes = classes;
        this.bindings = bindings;
        settings.forEach(setting -> setting.program = this);
        classes.forEach(klass -> {
            klass.program = this;
            klass.fields.forEach(field -> field.klass = klass);
            klass.implementations.forEach(implementation -> {
                implementation.klass = klass;
                implementation.calls.forEach(call -> {
                    call.implementation = implementation;
                    call.klass = getClass(call.signature.className);
                });
            });
        });
        bindings.forEach(binding -> {
            binding.program = this;
            binding.call = getCall(binding.callSignature);
            binding.implementation = getImplementation(binding.implementationSignature);
        });
    }

    Klass getClass(String className) {
        return classes.stream()
                .filter(klass -> klass.name.equals(className))
                .findFirst()
                .orElseThrow(() -> new RuntimeException("could not find class " + className));
    }

    Implementation getImplementation(Signature.Method signature) {
        Klass klass = getClass(signature.className);
        return klass.getImplementation(signature);
    }

    Call getCall(Signature.Call call) {
        return getImplementation(call.inSignature).getCall(call.toSignature);
    }

    Binding getBinding(Signature.Call callSignature, Signature.Method implementationSignature) {
        return bindings.stream()
                .filter(binding -> binding.callSignature.equals(callSignature) &&
                        binding.implementationSignature.equals(implementationSignature))
                .findFirst()
                .orElseThrow(() -> new RuntimeException(
                        "cound not find binding " + callSignature + " -> " + implementationSignature));
    }

    public String toString() {
        return "Program";
    }

    public String dump(int level) {
        return Utils.join(
                Utils.indentHeading(level, toString()),
                dumpList(settings, level + 1),
                dumpList(macros, level + 1),
                dumpList(classes, level + 1),
                dumpList(bindings, level + 1));
    }

    List<String> getSettingValues(String key) {
        return settings.stream()
                .filter(setting -> setting.key.equals(key))
                .map(setting -> setting.value)
                .collect(Collectors.toList());
    }

    public String getSettingValue(String key) {
        List<String> settings = getSettingValues(key);
        if (settings.size() == 0)
            return Program.Setting.defaultValues.get(key);
        String value = settings.get(settings.size() - 1);
        if (settings.size() > 1)
            Logger.warn("Found {} settings for key {}, using the latest value {}", settings.size(), key, value);
        return value;
    }

    public static class Setting implements Utils.Dumpable {
        static final String FALSE = "false";
        static final String TRUE = "true";
        static final String MODE = "mode";
        static final String MODE_HEADLESS = "headless";
        static final String MODE_GUI = "gui";
        static final String MODE_DEBUG = "debug";
        static final String OPTIMIZATION_STRATEGY = "optimization-strategy";
        static final String OPTIMIZATION_STRATEGY_NONE = "none";
        static final String OPTIMIZATION_STRATEGY_DEFAULT = "default";
        static final String OPTIMIZATION_STRATEGY_STRICT = "strict";
        static final String STRATEGY_PROPERTY = "strategy-property";
        static final String STORE_PROOF_CONTEXTS = "store-proof-contexts";
        static final String IS_DRY_RUN = "dry-run?";
        static final String LOG_LEVEL = "log-level";
        static final String TRACE = "trace";
        static final String DEBUG = "debug";
        static final String INFO = "info";
        static final String WARNING = "warning";
        static final String ERROR = "error";
        static final String OFF = "off";

        static final String[] allowedKeys = new String[]{
                MODE, OPTIMIZATION_STRATEGY, STRATEGY_PROPERTY, STORE_PROOF_CONTEXTS, IS_DRY_RUN, LOG_LEVEL
        };
        static final Map<String, String[]> allowedValues = new HashMap<>();
        static final String[] BOOLEAN_VALUES = {FALSE, TRUE};

        static {
            allowedValues.put(MODE, new String[]{MODE_HEADLESS, MODE_GUI, MODE_DEBUG});
            allowedValues.put(OPTIMIZATION_STRATEGY, new String[]{OPTIMIZATION_STRATEGY_NONE, OPTIMIZATION_STRATEGY_DEFAULT, OPTIMIZATION_STRATEGY_STRICT});
            allowedValues.put(STORE_PROOF_CONTEXTS, null);
            allowedValues.put(IS_DRY_RUN, BOOLEAN_VALUES);
            allowedValues.put(LOG_LEVEL, new String[]{TRACE, DEBUG, INFO, WARNING, ERROR, OFF});
        }
        static final Map<String, String> defaultValues = new HashMap<>();
        static {
            defaultValues.put(MODE, MODE_HEADLESS);
            defaultValues.put(OPTIMIZATION_STRATEGY, OPTIMIZATION_STRATEGY_DEFAULT);
            defaultValues.put(STORE_PROOF_CONTEXTS, null);
            defaultValues.put(IS_DRY_RUN, FALSE);
            defaultValues.put(LOG_LEVEL, TRACE);
        }

        public Program program;
        public String key;
        public String value;

        public Setting(String key, String value) {
            this.key = key;
            this.value = value;
            if (!Arrays.asList(allowedKeys).contains(key))
                throw new RuntimeException("invalid setting key " + key);
            if (allowedValues.get(key) != null && !Arrays.asList(allowedValues.get(key)).contains(value))
                throw new RuntimeException("invalid setting value " + value);
        }

        public String toString() {
            return String.format("Setting[%s, %s]", key, value);
        }
    }

    public static class Klass implements Utils.Dumpable {
        public Program program;
        public String name;
        public List<Field> fields;
        public List<Implementation> implementations;

        public Klass(String name, List<Field> fields, List<Implementation> implementations) {
            this.name = name;
            this.fields = fields;
            this.implementations = implementations;
        }

        Implementation getImplementation(Signature.Method signature) {
            List<Implementation> implementations = this.implementations.stream()
                    .filter(implementation -> implementation.signature.matches(signature))
                    .collect(Collectors.toList());
            if (implementations.size() > 1)
                throw new IllegalArgumentException("more than one implementation found for signature " + signature);
            return implementations.stream()
                    .findFirst()
                    .orElseThrow(() -> new IllegalArgumentException("no implementation found for signature " + signature));
        }

        public String toString() {
            return String.format("Class[%s]", name);
        }

        public String dump(int level) {
            return Utils.join(
                    Utils.indent(level) + toString(),
                    dumpList(fields, level + 1),
                    dumpList(implementations, level + 1));
        }
    }

    public static class Field implements Utils.Dumpable {
        public Klass klass;
        public Signature.Field signature;

        public Field(Signature.Field signature) {
            this.signature = signature;
        }

        public String toString() {
            return String.format("Field[%s]", signature);
        }
    }

    public static class Binding implements Utils.Dumpable {
        public Object clojureObject;
        public Program program;
        public Signature.Call callSignature;
        public Signature.Method implementationSignature;
        public Call call;
        public Implementation implementation;

        public Binding(Object clojureObject, Signature.Call callSignature, Signature.Method implementationSignature) {
            this.clojureObject = clojureObject;
            this.callSignature = callSignature;
            this.implementationSignature = implementationSignature;
        }

        public String toString() {
            return String.format("Binding[%s, %s]", call, implementation);
        }
    }

    public static class Implementation implements Utils.Dumpable {
        public Object clojureObject;
        public Klass klass;
        public Signature.Method signature;
        public String body;
        public String requires;
        public String ensures;
        public String assignable;
        public List<Call> calls;

        public Implementation(Object clojureObject, Signature.Method signature, String body, String requires,
                              String ensures, String assignable, List<Call> calls) {
            this.clojureObject = clojureObject;
            this.signature = signature;
            this.body = body;
            this.requires = requires;
            this.ensures = ensures;
            this.assignable = assignable;
            this.calls = calls;
        }

        List<Call> getExtendedCall(List<Binding> bindings) {
            return ClojureBridge.getExtendedCalls(klass.program, this, bindings);
        }

        Call getCall(Signature.Method signature) {
            List<Call> calls = this.calls.stream()
                    .filter(call -> call.signature.matches(signature))
                    .collect(Collectors.toList());
            if (calls.size() > 1)
                throw new IllegalArgumentException("more than one call found for signature " + signature);
            return calls.stream()
                    .findFirst()
                    .orElseThrow(() -> new IllegalArgumentException("no call found for signature " + signature));
        }

        public String toString() {
            return String.format("Implementation[%s]", signature);
        }

        public String dump(int level) {
            return Utils.join(
                    Utils.indent(level) + toString(),
                    dumpList(calls, level + 1));
        }
    }

    public static class Call implements Utils.Dumpable {
        public Implementation implementation;
        public Klass klass;
        public Signature.Method signature;

        public Call(Signature.Method signature) {
            this.signature = signature;
        }

        boolean isBoundBy(Binding binding) {
            return binding.call == this;
        }

        public String toString() {
            Signature.Call callSignature = new Signature.Call(implementation.signature, signature);
            return String.format("Call[%s]", callSignature);
        }

        private boolean isUsedInString(String string, String postfix) {
            return Macro.getMethodMacro(signature.name + postfix, null, new ArrayList<>()).isApplicable(string);
        }

        boolean isUsedInRequires(String postfix) {
            return isUsedInString(implementation.requires, postfix);
        }

        boolean isUsedInEnsures(String postfix) {
            return isUsedInString(implementation.ensures, postfix);
        }

        boolean isUsedInBody() {
            return isUsedInString(implementation.body, "");
        }

        Signature.Method getScopedSignature(boolean isContract, String postfix) {
            return (Signature.Method) signature.withName(
                    String.join("_",
                            signature.name + postfix,
                            "in",
                            implementation.signature.className,
                            implementation.signature.name,
                            isContract ? "contract" : "body"));
        }
    }

    public class ProofDescriptor implements Utils.Dumpable {
        public Program program;
        public Object clojureObject;
        public Implementation implementation;
        public Set<Binding> bindings;

        public ProofDescriptor(Object clojureObject, Signature.Method implementationSignature,
                               List<Utils.Pair<Signature.Call, Signature.Method>> bindings) {
            this.program = Program.this;
            this.clojureObject = clojureObject;
            this.implementation = getImplementation(implementationSignature);
            this.bindings = bindings.stream()
                    .map(pair -> getBinding(pair.first, pair.second))
                    .collect(Collectors.toSet());
        }

        public boolean isComplete() {
            return ClojureBridge.isComplete(this);
        }

        public String toString() {
            return String.format("ProofDescriptor[%s, %s (%d bindings)]",
                    implementation, isComplete() ? "complete" : "incomplete", bindings.size());
        }

        public String toCsv() {
            return ClojureBridge.toCsv(this);
        }

        public boolean equals(Object o) {
            if (this == o) return true;
            if (!(o instanceof ProofDescriptor)) return false;
            ProofDescriptor that = (ProofDescriptor) o;
            return Objects.equals(implementation, that.implementation) &&
                    Objects.equals(bindings, that.bindings);
        }

        public int hashCode() {
            return Objects.hash(implementation, bindings);
        }
    }

    public static class VerificationState implements Utils.Dumpable {
    }

    public class BeginProof extends VerificationState {
        public Implementation implementation;

        public BeginProof(Signature.Method implementationSignature) {
            this.implementation = getImplementation(implementationSignature);
        }

        public String toString() {
            return String.format("BeginProof[%s]", implementation);
        }
    }

    public class ContinueProof extends VerificationState {
        public ProofDescriptor proofDescriptor;
        public Binding binding;

        public ContinueProof(ProofDescriptor proofDescriptor,
                             Signature.Call srcSignature, Signature.Method dstSignature) {
            this.proofDescriptor = proofDescriptor;
            this.binding = getBinding(srcSignature, dstSignature);
        }

        public String toString() {
            return String.format("ContinueProof[%s, %s]", proofDescriptor, binding);
        }
    }

    public class ProofRepository implements Utils.Dumpable {
        public Program program;
        public List<Utils.Pair<Program.ProofDescriptor, Program.VerificationState>> proofMappings;

        public ProofRepository(List<Utils.Pair<Program.ProofDescriptor, Program.VerificationState>> proofMappings) {
            this.program = Program.this;
            this.proofMappings = proofMappings;
        }

        public String toString() {
            return "ProofRepository";
        }

        public String dump(int level) {
            return Utils.join(
                    Utils.indentHeading(level, toString()),
                    dumpList(proofMappings, level + 1));
        }
    }

    public static class Proof implements Utils.Dumpable {
        public final boolean isClosed;
        public String serializedProof;
        public Statistics statistics;
        public String proofContext;

        Proof(String serializedProof, Statistics statistics, boolean isClosed, String proofContext) {
            this.serializedProof = serializedProof;
            this.statistics = statistics;
            this.isClosed = isClosed;
            this.proofContext = proofContext;
        }

        public String toString() {
            return String.format("Proof[%s%s%s]",
                    isClosed ? "closed" : "open",
                    statistics != null ? " (" + statistics.nodes + " nodes, " + statistics.autoModeTimeInMillis + " ms)" : "",
                    proofContext != null ? ", " + proofContext : "");
        }
    }
}
