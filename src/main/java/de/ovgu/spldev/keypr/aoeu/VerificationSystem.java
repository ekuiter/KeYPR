package de.ovgu.spldev.keypr.aoeu;

import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collectors;

public interface VerificationSystem {
    interface IHoareTriple {
        Set<String> implementationCalls();
        Set<String> contractCalls();
    }

    interface IState {
    }

    IState beginProof(Model.Method method);

    default IState beginProof(Model.Method method, Set<Model.Binding> bindings) {
        IState verificationState = beginProof(method);
        for (Model.Binding binding : bindings) // nondeterministic!
            verificationState = continueProof(verificationState, binding);
        return verificationState;
    }

    default IState continueProof(IState verificationState, Model.Binding binding) {
        return continueProof(verificationState, Collections.singleton(binding));
    }

    default IState continueProof(IState verificationState, Set<Model.Binding> bindings) {
        // technically, this is not reproducible due to lack of set order
        for (Model.Binding binding : bindings)
            verificationState = continueProof(verificationState, binding);
        return verificationState;
    }

    boolean completeProof(IState verificationState);

    class Plain implements VerificationSystem {
        public static class HoareTriple implements IHoareTriple {
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

            @Override
            public Set<String> implementationCalls() {
                return implementationCalls;
            }

            @Override
            public Set<String> contractCalls() {
                return contractCalls;
            }
        }

        @Override
        public IState beginProof(Model.Method method) {
            return null;
        }

        @Override
        public IState continueProof(IState verificationState, Model.Binding binding) {
            return null;
        }

        @Override
        public boolean completeProof(IState verificationState) {
            return true;
        }
    }

    class KeY implements VerificationSystem {
        public static class HoareTriple implements IHoareTriple {
            String requires;
            String implementation;
            String ensures;
            String assignable;

            public HoareTriple(String requires, String implementation, String ensures, String assignable) {
                this.requires = requires;
                this.implementation = implementation;
                this.ensures = ensures;
                this.assignable = assignable;
            }

            @Override
            public Set<String> implementationCalls() {
                return null;
            }

            @Override
            public Set<String> contractCalls() {
                return null;
            }
        }

        public static class VerificationState implements IState {
        }

        @Override
        public IState beginProof(Model.Method method) {
            return null;
        }

        @Override
        public IState continueProof(IState verificationState, Model.Binding binding) {
            return null;
        }

        @Override
        public boolean completeProof(IState verificationState) {
            return true;
        }
    }
}
