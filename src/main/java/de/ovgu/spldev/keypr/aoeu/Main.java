package de.ovgu.spldev.keypr.aoeu;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;
import de.ovgu.featureide.fm.core.analysis.cnf.CNF;
import de.ovgu.featureide.fm.core.analysis.cnf.formula.FeatureModelFormula;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.AllConfigurationGenerator;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
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
import java.nio.file.Paths;
import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

public class Main {
    //static String featureIDEProject = "examples/HelloWorld-FH-JML";
    static String featureIDEProject = "examples/list";
    static VerificationSystem verificationSystem = new VerificationSystem.Plain();

    public static void main(String[] args) {
        LibraryManager.registerLibrary(FMCoreLibrary.getInstance());
        IFeatureModel featureModel = FeatureModelManager.load(Paths.get(featureIDEProject + "/model.xml"));
        CNF cnf = new FeatureModelFormula(featureModel).getCNF();
        Model.SoftwareProductLine spl = new Model.SoftwareProductLine(
                featureModel.getFeatureOrderList(), // this omits abstract features!
                LongRunningWrapper.runMethod(new AllConfigurationGenerator(cnf)).stream()
                        .map(literalSet -> new HashSet<>(cnf.getVariables().convertToString(literalSet))).collect(Collectors.toSet()),
                parseMethods(featureIDEProject));
        Model.BindingGraph bindingGraph = spl.program().prunedBindingGraph(spl);
        render(bindingGraph.toDot());
        Model.VerificationPlan verificationPlan = bindingGraph.someVerificationPlan().minify().optimize();
        render(verificationPlan.toDot());
        verificationPlan.verificationAttempt().verify(verificationSystem);
    }

    private static Set<Model.Method> parseMethods(String path) {
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
                                    // Assumption: If class A != class B and there are methods A.m1 and B.m2, m1 != m2.
                                    // Basically, this forbids late binding / polymorphism.
                                    methods.add(new Model.Method(feature, n.getName().asString(),
                                            new VerificationSystem.Plain.HoareTriple(implementationCalls, contractCalls)));
                                }
                            }.visit(compilationUnit, methods);
                        } catch (IOException ignored) {
                        }
                    });
                } catch (IOException ignored) {
                }
            });
        } catch (IOException ignored) {
        }
        methods.forEach(method -> method.hoareTriple.implementationCalls().retainAll(methodNames));
        return methods;
    }

    static String copy(String dot) {
        Toolkit.getDefaultToolkit().getSystemClipboard().setContents(new StringSelection(dot), null);
        return dot;
    }

    static void render(String dot) {
        BufferedImage image = Graphviz.fromString(copy(dot)).render(Format.PNG).toImage();
    }
}
