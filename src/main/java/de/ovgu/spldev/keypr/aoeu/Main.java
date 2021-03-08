package de.ovgu.spldev.keypr.aoeu;

import de.ovgu.featureide.fm.core.analysis.cnf.CNF;
import de.ovgu.featureide.fm.core.analysis.cnf.formula.FeatureModelFormula;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.AllConfigurationGenerator;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelElement;
import de.ovgu.featureide.fm.core.init.FMCoreLibrary;
import de.ovgu.featureide.fm.core.init.LibraryManager;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;
import guru.nidi.graphviz.engine.Format;
import guru.nidi.graphviz.engine.Graphviz;

import java.awt.*;
import java.awt.datatransfer.StringSelection;
import java.awt.image.BufferedImage;
import java.nio.file.Paths;
import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collectors;

public class Main {
    public static void main(String[] args) {
        LibraryManager.registerLibrary(FMCoreLibrary.getInstance());
        IFeatureModel featureModel = FeatureModelManager.load(Paths.get("HelloWorld-FH-JML/model.xml"));
        CNF cnf = new FeatureModelFormula(featureModel).getCNF();
        HashSet<Model.Method> methods = new HashSet<>();
        methods.add(new Model.Method("Hello", "print", new VerificationSystem.Plain.HoareTriple(new String[]{}, new String[]{})));
        methods.add(new Model.Method("Hello", "main", new VerificationSystem.Plain.HoareTriple(new String[]{"print"}, new String[]{})));
        methods.add(new Model.Method("Beautiful", "print", new VerificationSystem.Plain.HoareTriple(new String[]{"original"}, new String[]{"original"})));
        methods.add(new Model.Method("Wonderful", "print", new VerificationSystem.Plain.HoareTriple(new String[]{}, new String[]{"original"})));
        methods.add(new Model.Method("World", "print", new VerificationSystem.Plain.HoareTriple(new String[]{"original"}, new String[]{"original"})));
        Model.SoftwareProductLine spl = new Model.SoftwareProductLine(
                featureModel.getFeatureOrderList(),
                LongRunningWrapper.runMethod(new AllConfigurationGenerator(cnf)).stream()
                        .map(is -> new HashSet<>(cnf.getVariables().convertToString(is))).collect(Collectors.toSet()),
                methods);
        for (Set<String> c : spl.configurations) {
            System.out.println(c);
            System.out.println(spl.orderedConfiguration(c));
            System.out.println(spl.derivedMethods(c));
            System.out.println(spl.derivedBindings(c));
            System.out.println();
        }

//        List<String> features = new ArrayList<>();
//        features.add("List");
//        features.add("Ordered");
//        features.add("Set");
//        Set<Set<String>> configurations = new HashSet<>();
//        Set<String> c1 = new HashSet<>();
//        Set<String> c2 = new HashSet<>();
//        Set<String> c3 = new HashSet<>();
//        Set<String> c4 = new HashSet<>();
//        c1.add("List");
//        c2.add("List");
//        c2.add("Ordered");
//        c3.add("List");
//        c3.add("Set");
//        c4.add("List");
//        c4.add("Ordered");
//        c4.add("Set");
//        configurations.add(c1);
//        configurations.add(c2);
//        configurations.add(c3);
//        configurations.add(c4);
//        Set<Model.Method> methods = new HashSet<>();
//        methods.add(new Model.Method("List", "Insert", new VerificationSystem.Plain.HoareTriple(new String[]{}, new String[]{})));
//        methods.add(new Model.Method("List", "Search", new VerificationSystem.Plain.HoareTriple(new String[]{}, new String[]{})));
//        methods.add(new Model.Method("Ordered", "Insert", new VerificationSystem.Plain.HoareTriple(new String[]{"original", "Sort"}, new String[]{"original"})));
//        methods.add(new Model.Method("Ordered", "Search", new VerificationSystem.Plain.HoareTriple(new String[]{}, new String[]{"original"})));
//        methods.add(new Model.Method("Ordered", "Sort", new VerificationSystem.Plain.HoareTriple(new String[]{"Sort"}, new String[]{})));
//        methods.add(new Model.Method("Set", "Insert", new VerificationSystem.Plain.HoareTriple(new String[]{"original", "Search"}, new String[]{"original"})));
//        Model.SoftwareProductLine spl = new Model.SoftwareProductLine(features, configurations, methods);

        Model.BindingGraph bindingGraph = spl.program().prunedBindingGraph(spl);
        render(bindingGraph.toDot());
        Model.VerificationPlan verificationPlan = bindingGraph.someVerificationPlan().minify().optimize();
        render(verificationPlan.toDot());
        verificationPlan.verificationAttempt().verify(new VerificationSystem.Plain());
    }

    static String copy(String dot) {
        Toolkit.getDefaultToolkit().getSystemClipboard().setContents(new StringSelection(dot), null);
        return dot;
    }

    static void render(String dot) {
        BufferedImage image = Graphviz.fromString(copy(dot)).render(Format.PNG).toImage();
    }
}
