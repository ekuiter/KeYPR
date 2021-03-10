package de.ovgu.spldev.keypr.aoeu;

import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

public class Model {
    public static class Method {
        String feature;
        String name;
        VerificationSystem.HoareTriple hoareTriple;

        public Method(String feature, String name, VerificationSystem.HoareTriple hoareTriple) {
            this.feature = feature;
            this.name = name;
            this.hoareTriple = hoareTriple;
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

        Set<Call> implementationCalls() {
            return hoareTriple.implementationCalls().stream()
                    .map(call -> new Call(this, call))
                    .collect(Collectors.toSet());
        }

        Set<Call> contractCalls() {
            return hoareTriple.contractCalls().stream()
                    .map(call -> new Call(this, call))
                    .collect(Collectors.toSet());
        }

        Set<Call> calls() {
            Set<Call> calls = new HashSet<>(implementationCalls());
            calls.addAll(contractCalls());
            return calls;
        }

        Set<Call> extendedCalls(Set<Binding> bindings, int i) {
            if (bindings.isEmpty())
                return i == 0 ? calls() : contractCalls();
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
            List<String> orderedConfiguration = orderedConfiguration(restrictConfiguration(configuration, method));
            return !orderedConfiguration.isEmpty() && orderedConfiguration.get(orderedConfiguration.size() - 1).equals(feature);
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
                                        method.implementationCalls().contains(new Call(method, "original")) &&
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
            return String.format("%d", bindings.size());
        }

        public String toLongString() {
            return String.format("%s%s", method, bindings);
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

        public Edge(Node sourceNode, Node targetNode) {
            this.sourceNode = sourceNode;
            this.targetNode = targetNode;
        }

        Set<Binding> newBindings() {
            return targetNode.bindings.stream()
                    .filter(binding -> !sourceNode.bindings.contains(binding))
                    .collect(Collectors.toSet());
        }

        @Override
        public String toString() {
            return String.format("%s -%s-> %s", sourceNode, newBindings(), targetNode);
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;
            Edge edge = (Edge) o;
            return sourceNode.equals(edge.sourceNode) && targetNode.equals(edge.targetNode);
        }

        @Override
        public int hashCode() {
            return Objects.hash(sourceNode, targetNode);
        }
    }

    public static class BindingGraph {
        Set<Node> nodes = new HashSet<>();
        Set<Edge> edges = new HashSet<>();

        public BindingGraph(Set<Node> nodes) {
            this.nodes = new HashSet<>(nodes);
            this.edges = inferEdges(nodes);
        }

        public BindingGraph(BindingGraph bindingGraph) {
            this.nodes = new HashSet<>(bindingGraph.nodes);
            this.edges = new HashSet<>(bindingGraph.edges);
        }

        public BindingGraph() {
        }

        static Set<Edge> inferEdges(Set<Node> nodes) {
            return nodes.stream().flatMap(targetNode -> nodes.stream()
                    .filter(sourceNode -> targetNode.method.equals(sourceNode.method) &&
                            targetNode.bindings.containsAll(sourceNode.bindings) &&
                            targetNode.bindings.size() == sourceNode.bindings.size() + 1)
                    .map(sourceNode -> new Edge(sourceNode, targetNode))).collect(Collectors.toSet());
        }

        String toDot(Set<Node> focusNodes, Set<Edge> focusEdges) {
            return String.format("digraph {\n" +
                            "rankdir = LR;\n" +
                            "%s\n" +
                            "%s\n" +
                            "%s\n" +
                            "}",
                    nodes.stream().map(node -> node.method).distinct().map(method ->
                            String.format("subgraph \"cluster_%s\" {\n" +
                                    "label = \"%s\";\n" +
                                    "%s\n" +
                                    "}\n",
                                    method,
                                    method,
                                    nodes.stream()
                                            .filter(node -> node.method.equals(method))
                                            .map(node -> String.format(
                                                    "\"%s\" [label = \"%s\", tooltip = \"%s\", style = \"%s\"];",
                                                    node.id, node.toShortString(), node.toLongString(),
                                                    focusNodes != null && !focusNodes.contains(node) ? "invis" :
                                                            node.isComplete() ? "diagonals" : "solid"))
                                            .collect(Collectors.joining("\n"))))
                            .collect(Collectors.joining("\n")),
                    edges.stream().map(edge -> String.format("\"%s\" -> \"%s\" [tooltip = \"%s\"%s];",
                            edge.sourceNode.id, edge.targetNode.id, edge.newBindings(),
                            (focusEdges != null && !focusEdges.contains(edge) ? ", style = \"invis\"" : "")))
                            .collect(Collectors.joining("\n")),
                    (focusEdges != null ? focusEdges : new HashSet<Edge>()).stream()
                            .filter(edge -> !edges.contains(edge))
                            .map(edge -> String.format("\"%s\" -> \"%s\" [tooltip = \"%s\"];",
                                    edge.sourceNode.id, edge.targetNode.id, edge.newBindings()))
                            .collect(Collectors.joining("\n")));
        }

        public String toDot() {
            return toDot(null, null);
        }

        VerificationPlan someVerificationPlan() {
            return new VerificationPlanGenerator(this).iterator().next();
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
            this.bindingGraph = new BindingGraph(bindingGraph);
            this.nodes = new HashSet<>(nodes);
            this.edges = new HashSet<>(edges);
        }

        public String toDot() {
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

        VerificationPlan optimize() {
            VerificationPlan verificationPlan = new VerificationPlan(bindingGraph, nodes, edges);
            boolean done = false;
            while (!done) {
                Node removeNode = verificationPlan.nodes.stream()
                        .filter(node -> verificationPlan.edges.stream()
                                .filter(edge -> edge.sourceNode.equals(node)).count() == 1)
                        .findAny().orElse(null);
                if (removeNode != null) {
                    Edge parentEdge = verificationPlan.edges.stream().filter(edge -> edge.targetNode.equals(removeNode))
                            .findFirst().orElse(null);
                    Edge childEdge = verificationPlan.edges.stream().filter(edge -> edge.sourceNode.equals(removeNode))
                            .findFirst().get();
                    if (parentEdge != null) {
                        verificationPlan.edges.add(new Edge(parentEdge.sourceNode, childEdge.targetNode));
                        verificationPlan.edges.remove(parentEdge);
                    }
                    verificationPlan.edges.remove(childEdge);
                    verificationPlan.nodes.remove(removeNode);
                } else
                    done = true;
            }
            verificationPlan.bindingGraph.nodes = verificationPlan.nodes;
            verificationPlan.bindingGraph.edges = verificationPlan.edges;
            return verificationPlan;
        }

        VerificationAttempt verificationAttempt() {
            return new VerificationAttempt(this);
        }
    }

    public static class VerificationPlanGenerator implements Iterable<VerificationPlan> {
        BindingGraph bindingGraph;
        List<List<Edge>> edgeFamily;

        public VerificationPlanGenerator(BindingGraph bindingGraph) {
            this.bindingGraph = bindingGraph;
            edgeFamily = bindingGraph.nodes.stream()
                    .map(node -> bindingGraph.edges.stream().filter(edge -> edge.targetNode.equals(node))
                            .collect(Collectors.toList()))
                    .filter(edges -> !edges.isEmpty()).collect(Collectors.toList());
        }

        @Override
        public Iterator<VerificationPlan> iterator() {
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

    public static class VerificationAttempt {
        VerificationPlan verificationPlan;
        List<Node> sortedNodes;
        Map<Node, VerificationSystem.State> map = new HashMap<>();

        public VerificationAttempt(VerificationPlan verificationPlan) {
            this.verificationPlan = verificationPlan;
            // this is ONE topological sorting, others are possible.
            // this is not interesting if we restrict ourselves to one core and no network partitions.
            this.sortedNodes = verificationPlan.nodes.stream()
                    .sorted(Comparator.comparing(node -> node.bindings.size()))
                    .collect(Collectors.toList());
        }

        @Override
        public String toString() {
            return sortedNodes.toString();
        }

        boolean verify(VerificationSystem verificationSystem) {
            for (Node node : sortedNodes) {
                if (verificationPlan.edges.stream().noneMatch(edge -> edge.targetNode.equals(node)))
                    map.put(node, verificationSystem.beginProof(node.method, node.bindings));
                else {
                    Edge edge = verificationPlan.edges.stream()
                            .filter(_edge -> _edge.targetNode.equals(node))
                            .findFirst().get();
                    map.put(node, verificationSystem.continueProof(map.get(edge.sourceNode), edge.newBindings()));
                }
            }
            return isCorrect(verificationSystem);
        }

        boolean isCorrect(VerificationSystem verificationSystem) {
            return sortedNodes.stream().filter(Node::isComplete).map(map::get)
                    .allMatch(verificationSystem::completeProof);
        }
    }
}
