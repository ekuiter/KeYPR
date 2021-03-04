package de.ovgu.spldev.keypr.aoeu;

import java.awt.*;
import java.awt.datatransfer.StringSelection;
import java.util.*;
import java.util.List;

public class Main {
    public static void main(String[] args) {
        List<String> features = new ArrayList<>();
        features.add("List");
        features.add("Ordered");
        features.add("Set");
        Set<Set<String>> configurations = new HashSet<>();
        Set<String> c1 = new HashSet<>();
        Set<String> c2 = new HashSet<>();
        Set<String> c3 = new HashSet<>();
        Set<String> c4 = new HashSet<>();
        c1.add("List");
        c2.add("List");
        c2.add("Ordered");
        c3.add("List");
        c3.add("Set");
        c4.add("List");
        c4.add("Ordered");
        c4.add("Set");
        configurations.add(c1);
        configurations.add(c2);
        configurations.add(c3);
        configurations.add(c4);
        Set<Model.Method> methods = new HashSet<>();
        methods.add(new Model.Method("List", "Insert", "", "", "", "", new String[]{}, new String[]{}));
        methods.add(new Model.Method("List", "Search", "", "", "", "", new String[]{}, new String[]{}));
        methods.add(new Model.Method("Ordered", "Insert", "", "", "", "", new String[]{"original", "Sort"}, new String[]{"original"}));
        methods.add(new Model.Method("Ordered", "Search", "", "", "", "", new String[]{}, new String[]{"original"}));
        methods.add(new Model.Method("Ordered", "Sort", "", "", "", "", new String[]{"Sort"}, new String[]{}));
        methods.add(new Model.Method("Set", "Insert", "", "", "", "", new String[]{"original", "Search"}, new String[]{"original"}));
        Model.SoftwareProductLine spl = new Model.SoftwareProductLine(features, configurations, methods);
        Model.Program program = spl.program();
        Model.BindingGraph bindingGraph = program.prunedBindingGraph(spl);
        //Model.SpanningForestVerificationPlan spanningForestVerificationPlan = new Model.MinimumSpanningForestVerificationPlan(bindingGraph);
        Model.SpanningForestVerificationPlanGenerator spanningForestVerificationPlanGenerator = new Model.SpanningForestVerificationPlanGenerator(bindingGraph);
        for (Model.VerificationPlan verificationPlan : spanningForestVerificationPlanGenerator) {
            copy(verificationPlan.minify().toDot());
        }
    }

    static void copy(String str) {
        Toolkit.getDefaultToolkit().getSystemClipboard().setContents(new StringSelection(str), null);
    }

    // idea: summarize multiple nodes in one to avoid partial proofs (batch bindings)
    // one extreme: KeY as is, other extreme: KeY with abstract contracts
    // the study of these graphs/trees is worth its own paper.
}
