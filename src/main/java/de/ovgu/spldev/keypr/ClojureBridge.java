package de.ovgu.spldev.keypr;

import java.util.Collection;
import java.util.List;
import java.util.stream.Collectors;

class ClojureBridge {
    private static final String CORE_NS = "clojure.core";
    private static final String KEYPR_NS = "de.ovgu.spldev.keypr";
    private static final String KEYPR_CLJ = "@de/ovgu/spldev/keypr.clj";

    static void repl(String form) {
    }

    private static Object call(String namespace, String function, Object... args) {
        return null;
    }

    private static Object call(String function, Object... args) {
        return call(KEYPR_NS, function, args);
    }

    private static <T> Object toSet(Collection<T> collection) {
        return null;
    }

    static List<Program.Call> getExtendedCalls(
            Program program, Program.Implementation implementation, List<Program.Binding> bindings) {
        @SuppressWarnings("unchecked") List<Signature.Call> extendedCallSignatures =
                (List<Signature.Call>) call("->ExtendedCallSignatures",
                        program.clojureObject, 0, implementation.clojureObject,
                        toSet(bindings.stream().map(binding -> binding.clojureObject).collect(Collectors.toSet())));
        return extendedCallSignatures.stream().map(program::getCall).collect(Collectors.toList());
    }

    static boolean isComplete(Program.ProofDescriptor proofDescriptor) {
        return (boolean) call("proof-descriptor-complete?",
                proofDescriptor.program.clojureObject, proofDescriptor.clojureObject);
    }

    static String toCsv(Program.ProofDescriptor proofDescriptor) {
        return (String) call("proof-descriptor->csv", proofDescriptor.clojureObject);
    }
}
