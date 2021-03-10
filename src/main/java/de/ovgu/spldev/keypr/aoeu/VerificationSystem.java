package de.ovgu.spldev.keypr.aoeu;

import java.util.Arrays;
import java.util.Collections;
import java.util.Set;
import java.util.stream.Collectors;

public class VerificationSystem {
    public static class HoareTriple {
        Set<String> implementationCalls;
        Set<String> contractCalls;

        public HoareTriple(Set<String> implementationCalls, Set<String> contractCalls) {
            this.implementationCalls = implementationCalls;
            this.contractCalls = contractCalls;
        }

        public HoareTriple(String[] implementationCalls, String[] contractCalls) {
            this(Arrays.stream(implementationCalls).collect(Collectors.toSet()),
                    Arrays.stream(contractCalls).collect(Collectors.toSet()));
        }

        public Set<String> implementationCalls() {
            return implementationCalls;
        }

        public Set<String> contractCalls() {
            return contractCalls;
        }
    }

    public static class State {
    }

    State beginProof(Model.Method method) {
        return null;
    }

    State beginProof(Model.Method method, Set<Model.Binding> bindings) {
        State state = beginProof(method);
        for (Model.Binding binding : bindings) // nondeterministic!
            state = continueProof(state, binding);
        return state;
    }

    State continueProof(State state, Model.Binding binding) {
        return null;
    }

    State continueProof(State state, Set<Model.Binding> bindings) {
        // technically, this is not reproducible due to lack of set order
        for (Model.Binding binding : bindings)
            state = continueProof(state, binding);
        return state;
    }

    public boolean completeProof(State state) {
        return true;
    }

    static class KeY extends VerificationSystem {
        public static class HoareTriple extends VerificationSystem.HoareTriple {
            String requires;
            String implementation;
            String ensures;
            String assignable;

            public HoareTriple(Set<String> implementationCalls, Set<String> contractCalls,
                               String requires, String implementation, String ensures, String assignable) {
                super(implementationCalls, contractCalls);
                this.requires = requires;
                this.implementation = implementation;
                this.ensures = ensures;
                this.assignable = assignable;
            }
        }

        public static class State extends VerificationSystem.State {
        }

        public State beginProof(Model.Method method) {
            return null;
        }

        public State continueProof(State state, Model.Binding binding) {
            return null;
        }

        public boolean completeProof(State state) {
            return true;
        }
    }
}
