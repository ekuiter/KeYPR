package de.ovgu.spldev.keypr.aoeu;

import org.jetbrains.annotations.NotNull;

import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

public class Model {
    public static class Method {
        String feature;
        String name;
        String requires;
        String implementation;
        String ensures;
        String assignable;
        Set<Call> implementationCalls;
        Set<Call> contractCalls;

        public Method(String feature, String name, String requires, String implementation, String ensures,
                      String assignable, String[] implementationCalls, String[] contractCalls) {
            this.feature = feature;
            this.name = name;
            this.requires = requires;
            this.implementation = implementation;
            this.ensures = ensures;
            this.assignable = assignable;
            this.implementationCalls = Arrays.stream(implementationCalls)
                    .map(call -> new Call(this, call))
                    .collect(Collectors.toSet());
            this.contractCalls = Arrays.stream(contractCalls)
                    .map(call -> new Call(this, call))
                    .collect(Collectors.toSet());
        }

        @Override
        public String toString() {
            return String.format("%s::%s", feature, name);
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;
            Method method = (Method) o;
            return feature.equals(method.feature) && name.equals(method.name);
        }

        @Override
        public int hashCode() {
            return Objects.hash(feature, name);
        }

        Set<Call> calls() {
            Set<Call> calls = new HashSet<>(implementationCalls);
            calls.addAll(contractCalls);
            return calls;
        }

        Set<Call> extendedCalls(Set<Binding> bindings, int i) {
            if (bindings.isEmpty())
                return i == 0 ? calls() : contractCalls;
            else {
                Binding binding = bindings.iterator().next();
                Set<Binding> smallerBindings = new HashSet<>(bindings);
                smallerBindings.remove(binding);
                Set<Call> extendedCalls = new HashSet<>(extendedCalls(smallerBindings, i));
                if (extendedCalls.contains(binding.source))
                    extendedCalls.addAll(binding.destination.extendedCalls(smallerBindings, i + 1));
                return extendedCalls;
            }
        }

        Set<Call> extendedCalls(Set<Binding> bindings) {
            return extendedCalls(bindings, 0);
        }
    }

    public static class Call {
        Method in;
        String to;

        Call(Method in, String to) {
            this.in = in;
            this.to = to;
        }

        @Override
        public String toString() {
            return String.format("%s.%s", in, to);
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;
            Call call = (Call) o;
            return in.equals(call.in) && to.equals(call.to);
        }

        @Override
        public int hashCode() {
            return Objects.hash(in, to);
        }
    }

    public static class Binding {
        Call source;
        Method destination;

        public Binding(Call source, Method destination) {
            this.source = source;
            this.destination = destination;
        }

        @Override
        public String toString() {
            return String.format("%s -> %s", source, destination);
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;
            Binding binding = (Binding) o;
            return source.equals(binding.source) && destination.equals(binding.destination);
        }

        @Override
        public int hashCode() {
            return Objects.hash(source, destination);
        }
    }

    public static class SoftwareProductLine {
        List<String> features;
        Set<Set<String>> configurations;
        Set<Method> methods;

        public SoftwareProductLine(List<String> features, Set<Set<String>> configurations, Set<Method> methods) {
            this.features = features;
            this.configurations = new HashSet<>(configurations);
            this.methods = new HashSet<>(methods);
        }

        Comparator<Object> featureOrder() {
            return Comparator.comparing(feature -> IntStream.range(0, features.size())
                    .filter(i -> feature.equals(features.get(i))).findFirst().orElse(-1));
        }

        Set<Call> calls() {
            return methods.stream().flatMap(method -> method.calls().stream()).collect(Collectors.toSet());
        }

        boolean hasMethod(String feature, String name) {
            return methods.stream().anyMatch(method -> method.feature.equals(feature) && method.name.equals(name));
        }

        Set<String> restrictConfiguration(Set<String> configuration, String name) {
            return configuration.stream().filter(feature -> hasMethod(feature, name)).collect(Collectors.toSet());
        }

        List<String> orderedConfiguration(Set<String> configuration) {
            List<String> orderedConfiguration = new ArrayList<>(configuration);
            orderedConfiguration.sort(featureOrder());
            return orderedConfiguration;
        }

        boolean isLastFeature(Set<String> configuration, String feature, String method) {
            return orderedConfiguration(restrictConfiguration(configuration, method)).stream()
                    .reduce((first, second) -> second).stream().findFirst()
                    .map(feature::equals).orElse(false);
        }

        boolean isBeforeFeature(Set<String> configuration, String featureA, String featureB, String method) {
            List<String> orderedConfiguration = orderedConfiguration(restrictConfiguration(configuration, method));
            for (int i = 0; i < orderedConfiguration.size() - 1; i++)
                if (orderedConfiguration.get(i).equals(featureA))
                    return orderedConfiguration.get(i + 1).equals(featureB);
            return false;
        }

        Set<Method> derivedMethods(Set<String> configuration) {
            Set<Method> derivedMethods = methods.stream()
                    .filter(method -> isLastFeature(configuration, method.feature, method.name))
                    .collect(Collectors.toSet());
            boolean done = false;
            while (!done) {
                Set<Method> newDerivedMethods = derivedMethods.stream()
                        .flatMap(method -> methods.stream().filter(_method ->
                                _method.name.equals(method.name) &&
                                        method.implementationCalls.contains(new Call(method, "original")) &&
                                        isBeforeFeature(configuration, _method.feature, method.feature, method.name)))
                        .collect(Collectors.toSet());
                newDerivedMethods.removeAll(derivedMethods);
                derivedMethods.addAll(newDerivedMethods);
                done = newDerivedMethods.isEmpty();
            }
            return derivedMethods;
        }

        Set<Binding> derivedBindings(Set<String> configuration) {
            return calls().stream().flatMap(call -> {
                if (call.to.equals("original"))
                    return methods.stream().filter(method -> method.name.equals(call.in.name) &&
                            isBeforeFeature(configuration, method.feature, call.in.feature, method.name))
                            .map(method -> new Binding(call, method));
                else
                    return methods.stream().filter(method -> method.name.equals(call.to) &&
                            isLastFeature(configuration, method.feature, method.name))
                            .map(method -> new Binding(call, method));
            }).collect(Collectors.toSet());
        }

        Set<Binding> derivedBindings() {
            return configurations.stream().flatMap(configuration -> derivedBindings(configuration).stream())
                    .collect(Collectors.toSet());
        }

        Program program() {
            return new Program(methods, derivedBindings());
        }
    }

    public static class Program {
        Set<Method> methods;
        Set<Binding> bindings;

        public Program(Set<Method> methods, Set<Binding> bindings) {
            this.methods = new HashSet<>(methods);
            this.bindings = new HashSet<>(bindings);
        }

        static Set<Node> addBinding(Set<Node> nodes, Binding binding) {
            Set<Node> newNodes = new HashSet<>(nodes);
            newNodes.addAll(deltaAddBinding(nodes, binding));
            newNodes.addAll(nodes.stream().flatMap(node -> node.bindings.stream()
                    .flatMap(_binding -> addBinding(deltaAddBinding(nodes, binding), _binding).stream()))
                    .collect(Collectors.toSet()));
            return newNodes;
        }

        static Set<Node> deltaAddBinding(Set<Node> nodes, Binding binding) {
            return nodes.stream().filter(node -> node.unboundCalls().contains(binding.source)).map(node -> {
                Set<Binding> bindings = new HashSet<>(node.bindings);
                bindings.add(binding);
                return new Node(node.method, bindings);
            }).collect(Collectors.toSet());
        }

        Set<Node> bindingGraphNodes() {
            Set<Node> nodes = methods.stream().map(method -> new Node(method, new HashSet<>()))
                    .collect(Collectors.toSet());
            for (Binding binding : bindings)
                nodes = addBinding(nodes, binding);
            return nodes;
        }

        BindingGraph bindingGraph() {
            return new BindingGraph(bindingGraphNodes());
        }

        BindingGraph prunedBindingGraph(SoftwareProductLine softwareProductLine) {
            return new PrunedBindingGraph(softwareProductLine, bindingGraphNodes());
        }
    }

    public static class Node {
        static int idCounter = 0;
        int id;
        Method method;
        Set<Binding> bindings;

        public Node(Method method, Set<Binding> bindings) {
            this.id = idCounter++;
            this.method = method;
            this.bindings = new HashSet<>(bindings);
        }

        @Override
        public String toString() {
            return String.format("%s[%d]", method, bindings.size());
        }

        public String toShortString() {
            return bindings.isEmpty() ? method.toString() : bindings.size() + "";
        }

        public String toLongString() {
            return String.format("%s[%s]", method, bindings.stream().map(Binding::toString)
                    .collect(Collectors.joining(", ")));
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;
            Node node = (Node) o;
            return method.equals(node.method) && bindings.equals(node.bindings);
        }

        @Override
        public int hashCode() {
            return Objects.hash(method, bindings);
        }

        Set<Call> unboundCalls() {
            Set<Call> unboundCalls = new HashSet<>(method.extendedCalls(bindings));
            unboundCalls.removeAll(bindings.stream().map(binding -> binding.source).collect(Collectors.toSet()));
            return unboundCalls;
        }

        boolean isComplete() {
            return unboundCalls().isEmpty();
        }
    }

    public static class Edge {
        Node sourceNode;
        Node targetNode;
        Binding binding;

        public Edge(Node sourceNode, Node targetNode, Binding binding) {
            this.sourceNode = sourceNode;
            this.targetNode = targetNode;
            this.binding = binding;
        }

        @Override
        public String toString() {
            return String.format("%s -(%s)-> %s", sourceNode, binding, targetNode);
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;
            Edge edge = (Edge) o;
            return sourceNode.equals(edge.sourceNode) && targetNode.equals(edge.targetNode) &&
                    binding.equals(edge.binding);
        }

        @Override
        public int hashCode() {
            return Objects.hash(sourceNode, targetNode, binding);
        }
    }

    public static class BindingGraph {
        Set<Node> nodes = new HashSet<>();
        Set<Edge> edges = new HashSet<>();

        public BindingGraph(Set<Node> nodes) {
            this.nodes = new HashSet<>(nodes);
            this.edges = inferEdges(nodes);
        }

        public BindingGraph() {
        }

        static Set<Edge> inferEdges(Set<Node> nodes) {
            return nodes.stream().flatMap(targetNode -> nodes.stream()
                    .filter(sourceNode -> targetNode.method.equals(sourceNode.method) &&
                            targetNode.bindings.containsAll(sourceNode.bindings) &&
                            targetNode.bindings.size() == sourceNode.bindings.size() + 1)
                    .map(sourceNode -> {
                        Set<Binding> bindings = new HashSet<>(targetNode.bindings);
                        bindings.removeAll(sourceNode.bindings);
                        return new Edge(sourceNode, targetNode, bindings.iterator().next());
                    })).collect(Collectors.toSet());
        }

        String toDot(Set<Node> focusNodes, Set<Edge> focusEdges) {
            return String.format("digraph {\n" +
                            "rankdir = LR;\n" +
                            "graph [fontname = \"Handlee\"];\n" +
                            "node [fontname = \"Handlee\"];\n" +
                            "edge [fontname = \"Handlee\"];\n" +
                            "%s\n" +
                            "%s\n" +
                            "}",
                    nodes.stream().map(node -> String.format(
                            "\"%s\" [label = \"%s\", tooltip = \"%s\", style = \"%s\"];",
                            node.id, node.toShortString(), node.toLongString(),
                            focusNodes != null && !focusNodes.contains(node) ? "invis" :
                                    node.isComplete() ? "diagonals,bold" : "solid"))
                            .collect(Collectors.joining("\n")),
                    edges.stream().map(edge -> String.format("\"%s\" -> \"%s\" [tooltip = \"%s\"%s];",
                            edge.sourceNode.id, edge.targetNode.id, edge.binding,
                            (focusEdges != null && !focusEdges.contains(edge) ? ", style = \"invis\"" : "")))
                            .collect(Collectors.joining("\n")));
        }

        String toDot() {
            return toDot(null, null);
        }
    }

    public static class PrunedBindingGraph extends BindingGraph {
        public PrunedBindingGraph(SoftwareProductLine softwareProductLine, Set<Node> nodes) {
            this.nodes = prune(softwareProductLine, nodes);
            this.edges = inferEdges(this.nodes);
        }

        Set<Node> prune(SoftwareProductLine softwareProductLine, Set<Node> nodes) {
            return nodes.stream().filter(node -> softwareProductLine.configurations.stream()
                    .anyMatch(configuration ->
                            softwareProductLine.derivedMethods(configuration).contains(node.method) &&
                                    softwareProductLine.derivedBindings(configuration).containsAll(node.bindings)))
                    .collect(Collectors.toSet());
        }
    }

    public static class VerificationPlan {
        BindingGraph bindingGraph;
        Set<Node> nodes;
        Set<Edge> edges;

        public VerificationPlan(BindingGraph bindingGraph, Set<Node> nodes, Set<Edge> edges) {
            this.bindingGraph = bindingGraph;
            this.nodes = new HashSet<>(nodes);
            this.edges = new HashSet<>(edges);
        }

        String toDot() {
            return bindingGraph.toDot(nodes, edges);
        }

        VerificationPlan minify() {
            VerificationPlan verificationPlan = new VerificationPlan(bindingGraph, nodes, edges);
            boolean done = false;
            while (!done) {
                Set<Node> removeNodes = verificationPlan.nodes.stream()
                        .filter(node -> verificationPlan.edges.stream().noneMatch(edge -> edge.sourceNode.equals(node)))
                        .filter(node -> !node.isComplete())
                        .collect(Collectors.toSet());
                verificationPlan.edges.removeAll(verificationPlan.edges.stream()
                        .filter(edge -> removeNodes.stream().anyMatch(node -> edge.targetNode.equals(node)))
                        .collect(Collectors.toSet()));
                verificationPlan.nodes.removeAll(removeNodes);
                done = removeNodes.isEmpty();
            }
            return verificationPlan;
        }
    }

    public static class SpanningForestVerificationPlanGenerator implements Iterable<VerificationPlan> {
        BindingGraph bindingGraph;
        List<List<Edge>> edgeFamily;

        public SpanningForestVerificationPlanGenerator(BindingGraph bindingGraph) {
            this.bindingGraph = bindingGraph;
            edgeFamily = bindingGraph.nodes.stream()
                    .map(node -> bindingGraph.edges.stream().filter(edge -> edge.targetNode.equals(node))
                            .collect(Collectors.toList()))
                    .filter(edges -> !edges.isEmpty()).collect(Collectors.toList());
        }

        @Override
        public @NotNull Iterator<VerificationPlan> iterator() {
            return new Iterator<VerificationPlan>() {
                final int[] indices = new int[edgeFamily.size()];
                boolean done = false;

                void increment() {
                    if (indices.length == 0) {
                        done = true;
                        return;
                    }
                    int i = 0;
                    indices[i]++;
                    while (indices[i] >= edgeFamily.get(i).size()) {
                        indices[i] = 0;
                        i++;
                        if (i >= indices.length) {
                            done = true;
                            return;
                        }
                        indices[i]++;
                    }
                }

                @Override
                public boolean hasNext() {
                    return !done;
                }

                @Override
                public VerificationPlan next() {
                    Set<Edge> edges = new HashSet<>();
                    for (int i = 0; i < indices.length; i++) {
                        edges.add(edgeFamily.get(i).get(indices[i]));
                    }
                    increment();
                    return new VerificationPlan(bindingGraph, bindingGraph.nodes, edges);
                }
            };
        }
    }
}
