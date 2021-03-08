package de.ovgu.spldev.keypr.aoeu;

import com.github.javaparser.JavaParser;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.comments.BlockComment;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;
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
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.*;
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.Stream;

public class Main {
    public static void main(String[] args) {

        String path = "examples/HelloWorld-FH-JML";

        LibraryManager.registerLibrary(FMCoreLibrary.getInstance());
        IFeatureModel featureModel = FeatureModelManager.load(Paths.get(path + "/model.xml"));
        CNF cnf = new FeatureModelFormula(featureModel).getCNF();
//        HashSet<Model.Method> methods_ = new HashSet<>();
//        methods_.add(new Model.Method("Hello", "HelloWorld::print", new VerificationSystem.Plain.HoareTriple(new String[]{}, new String[]{})));
//        methods_.add(new Model.Method("Hello", "HelloWorld::main", new VerificationSystem.Plain.HoareTriple(new String[]{"HelloWorld::print"}, new String[]{})));
//        methods_.add(new Model.Method("Beautiful", "HelloWorld::print", new VerificationSystem.Plain.HoareTriple(new String[]{"original"}, new String[]{"original"})));
//        methods_.add(new Model.Method("Wonderful", "HelloWorld::print", new VerificationSystem.Plain.HoareTriple(new String[]{}, new String[]{"original"})));
//        methods_.add(new Model.Method("World", "HelloWorld::print", new VerificationSystem.Plain.HoareTriple(new String[]{"original"}, new String[]{"original"})));

        Set<String> methodNames = Stream.of("original").collect(Collectors.toSet());
        Set<Model.Method> methods = new HashSet<>();
        try {
            Files.walk(Paths.get(path + "/features"), 1).forEach(directory -> {
                String feature = directory.getFileName().toString();
                if (feature.equals("features"))
                    return;
                try {
                    Files.walk(Paths.get(path + "/features/" + feature)).forEach(file -> {
                        try {
                            String klass = file.getFileName().toString().replace(".java", "");
                            CompilationUnit compilationUnit = StaticJavaParser.parse(file);
                            new VoidVisitorAdapter<Set<Model.Method>>() {
                                @Override
                                public void visit(MethodDeclaration n, Set<Model.Method> methods) {
                                    super.visit(n, methods);
                                    Set<String> implementationCalls = new HashSet<>(), contractCalls = new HashSet<>();
                                    Node.BreadthFirstIterator bfi = new Node.BreadthFirstIterator(n);
                                    while (bfi.hasNext()) {
                                        Node n2 = bfi.next();
                                        if (n2 instanceof MethodCallExpr) {
                                            implementationCalls.add(((MethodCallExpr) n2).getName().asString());
                                        }
                                    }
                                    n.getComment().ifPresent(comment -> {
                                        if (comment.getContent().contains("\\original"))
                                            contractCalls.add("original");
                                    });
                                    methodNames.add(n.getName().asString());
                                    // Assumption: if class A != class B and there are methods A.m1 and B.m2, m1 != m2.
                                    methods.add(new Model.Method(feature, n.getName().asString(),
                                            new VerificationSystem.Plain.HoareTriple(implementationCalls, contractCalls)));
                                }
                            }.visit(compilationUnit, methods);
                        } catch (IOException e) {
                        }
                    });
                } catch (IOException e) {
                }
            });
        } catch (IOException e) {
        }
        methods.forEach(method -> method.hoareTriple.implementationCalls().retainAll(methodNames));

        Model.SoftwareProductLine spl = new Model.SoftwareProductLine(
                featureModel.getFeatureOrderList(), // this omits abstract features!
                LongRunningWrapper.runMethod(new AllConfigurationGenerator(cnf)).stream()
                        .map(literalSet -> new HashSet<String>(cnf.getVariables().convertToString(literalSet))).collect(Collectors.toSet()),
                methods);

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
