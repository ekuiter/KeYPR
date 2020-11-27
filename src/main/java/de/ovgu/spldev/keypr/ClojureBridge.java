package de.ovgu.spldev.keypr;

import clojure.java.api.Clojure;
import clojure.lang.IFn;
import org.pmw.tinylog.Logger;

import java.util.Collection;
import java.util.List;
import java.util.stream.Collectors;

class ClojureBridge {
    private static final String CORE_NS = "clojure.core";
    private static final String KEYPR_NS = "de.ovgu.spldev.keypr";
    private static final String KEYPR_CLJ = "@de/ovgu/spldev/keypr.clj";

    static {
        Logger.info("Initializing Clojure bridge");
        call(CORE_NS, "require", Clojure.read(KEYPR_NS));
    }

    static void repl(String form) {
        clojure.main.main(new String[]{"-i", KEYPR_CLJ, "-e", "(ns " + KEYPR_NS + ") " + form});
    }

    private static Object call(String namespace, String function, Object... args) {
        IFn fn = Clojure.var(namespace, function);
        if (args.length == 0)
            return fn.invoke();
        if (args.length == 1)
            return fn.invoke(args[0]);
        if (args.length == 2)
            return fn.invoke(args[0], args[1]);
        if (args.length == 3)
            return fn.invoke(args[0], args[1], args[2]);
        if (args.length == 4)
            return fn.invoke(args[0], args[1], args[2], args[3]);
        throw new RuntimeException("too many arguments for Clojure call");
    }

    private static Object call(String function, Object... args) {
        return call(KEYPR_NS, function, args);
    }

    private static <T> Object toSet(Collection<T> collection) {
        return call(CORE_NS, "into", Clojure.read("#{}"), collection);
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
