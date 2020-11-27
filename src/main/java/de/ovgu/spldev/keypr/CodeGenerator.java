package de.ovgu.spldev.keypr;

import java.util.*;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.Stream;

public class CodeGenerator {
    public static final String RESULT_KEYWORD = "_result";
    public static final String ORIGINAL_KEYWORD = "original";
    public static final String PRE_KEYWORD = "_pre";
    public static final String POST_KEYWORD = "_post";

    private final Program program;
    private final boolean useAbstractContracts;

    public CodeGenerator(Program program, boolean useAbstractContracts) {
        this.program = program;
        this.useAbstractContracts = useAbstractContracts;
    }

    private String applyMacros(String str) {
        return Macro.applyMacros(str, program.macros);
    }

    private boolean isEnsures(Boolean isRequires) {
        return isRequires != null && !isRequires;
    }

    private String getBareMethodName(Signature signature) {
        String[] parts = signature.className.split("_");
        if (parts.length < 2)
            throw new RuntimeException("expected feature name");
        return String.join("_", Arrays.copyOfRange(parts, 1, parts.length));
    }

    private String getResultExpression(Boolean isRequires, Signature signature, boolean isModelBehavior, boolean isConcrete) {
        return !isModelBehavior && !isConcrete && !isRequires ? "\\result" : RESULT_KEYWORD + "_" + getBareMethodName(signature);
    }

    private List<String> getPrependParameters(Boolean isRequires, Signature.Method signature, boolean isModelBehavior, boolean isConcrete) {
        return Collections.singletonList(getResultExpression(isRequires, signature, isModelBehavior, isConcrete));
    }

    private String getScopedString(String string, Program.Implementation implementation, Boolean isRequires, boolean isModelBehavior, boolean isConcrete) {
        if (isEnsures(isRequires))
            string = new Macro(RESULT_KEYWORD, getResultExpression(isRequires, implementation.signature, isModelBehavior, isConcrete), true).apply(string);
        if (isRequires != null)
            string = string.replace("\n", " ");
        for (Program.Call call : implementation.calls) {
            if (isRequires == null)
                string = Macro
                        .getMethodMacro(call.signature.name, call.getScopedSignature(false, "").name, new ArrayList<>())
                        .apply(string);
            if (isRequires != null) {
                string = Macro
                        .getMethodMacro(call.signature.name + PRE_KEYWORD, call.getScopedSignature(true, PRE_KEYWORD).name,
                                getPrependParameters(isRequires, implementation.signature, isModelBehavior, isConcrete))
                        .apply(string);
                string = Macro
                        .getMethodMacro(call.signature.name + POST_KEYWORD, call.getScopedSignature(true, POST_KEYWORD).name,
                                getPrependParameters(isRequires, implementation.signature, isModelBehavior, isConcrete))
                        .apply(string);
            }
        }
        return string;
    }

    String getRequires(Program.Implementation implementation, boolean isModelBehavior, boolean isConcrete) {
        String requires = applyMacros(implementation.requires);
        return getScopedString(requires, implementation, true, isModelBehavior, isConcrete);
    }

    String getEnsures(Program.Implementation implementation, boolean isModelBehavior, boolean isConcrete) {
        String ensures = applyMacros(implementation.ensures);
        return getScopedString(ensures, implementation, false, isModelBehavior, isConcrete);
    }

    String getBody(Program.Implementation implementation) {
        String body = applyMacros(implementation.body);
        return getScopedString(body, implementation, null, false, true);
    }

    private String generateContract(@SuppressWarnings("SameParameterValue") String preamble, String... args) {
        if (args.length % 2 != 0)
            throw new IllegalArgumentException("expected map of JML keywords to values");
        StringBuilder sb = new StringBuilder();
        sb.append("/*@ ").append(preamble).append("\n");
        for (int i = 0; i < args.length; i += 2)
            sb.append("  @ ").append(args[i]).append(" ").append(args[i + 1]).append("\n");
        return sb.append("  @*/\n").toString();
    }

    private String generateJavaMethodWithContract(String contract, Signature.Method signature, String body) {
        return contract + signature.toJava() + " {\n" + body + "\n}\n";
    }

    private String generateJavaMethodWithContractAndBody(String contract, Signature.Method signature, Program.Implementation implementation) {
        return generateJavaMethodWithContract(contract, signature, getBody(implementation));
    }

    private String generateJavaMethodWithContractAndEmptyBody(String contract, Signature.Method signature) {
        return generateJavaMethodWithContract(contract, signature, "");
    }

    private String generateModelMethod(Signature.Method signature, String ensuresDef) {
        signature = (Signature.Method) signature
                .prependParameters(Collections.singletonList(new Utils.Pair<>(signature.type, RESULT_KEYWORD + "_" + getBareMethodName(signature))))
                .asBoolean();
        Placeholder placeholder = new Placeholder(signature, useAbstractContracts, true);
        return placeholder.generateModelBehaviorContract(ensuresDef);
    }

    private String generateDefinedModelMethod(Signature.Method signature, Program.Implementation implementation) {
        return generateModelMethod(
                signature.withParameters(implementation.signature),
                signature.name.startsWith(ORIGINAL_KEYWORD + PRE_KEYWORD)
                        ? getRequires(implementation, true, false)
                        : signature.name.startsWith(ORIGINAL_KEYWORD + POST_KEYWORD)
                        ? getEnsures(implementation, true, false)
                        : null);
    }

    private String generateUndefinedModelMethod(Signature.Method signature) {
        return generateModelMethod(signature, null);
    }

    private String generateDefinedJavaMethod(Signature.Method signature, Program.Implementation implementation) {
        signature = signature.withParameters(implementation.signature);
        Placeholder placeholder = new Placeholder(signature, useAbstractContracts, false);
        return generateJavaMethodWithContractAndEmptyBody(
                placeholder.generateNormalBehaviorContract(
                        getRequires(implementation, false, false),
                        getEnsures(implementation, false, false),
                        "\\nothing"),
                signature);
    }

    private String generateUndefinedJavaMethod(Signature.Method signature) {
        return generateJavaMethodWithContractAndEmptyBody(
                new Placeholder(signature, useAbstractContracts, false)
                        .generateNormalBehaviorContract(null, null, "\\nothing"),
                signature);
    }

    private String generateConcreteJavaMethod(Program.Implementation implementation) {
        Placeholder placeholder = new Placeholder(implementation.signature, false, false);
        return generateJavaMethodWithContractAndBody(
                placeholder.generateNormalBehaviorContract(
                        getRequires(implementation, false, true),
                        getEnsures(implementation, false, true),
                        implementation.assignable),
                implementation.signature,
                implementation);
    }

    @SuppressWarnings("Convert2MethodRef")
    private Stream<String> generateFields(Program.Implementation implementation, String methods) {
        return Stream.concat(
                program.classes.stream().map(_klass -> {
                    //noinspection OptionalGetWithoutIsPresent
                    Program.Field field = _klass.fields.stream()
                            .filter(_field -> _field.signature.name.equals(RESULT_KEYWORD))
                            .findFirst().get();
                    return field.signature.withName(RESULT_KEYWORD + "_" + getBareMethodName(field.signature));
                }).filter(signature -> signature.name.equals(RESULT_KEYWORD + "_" + getBareMethodName(implementation.signature))
                        || !methods.replace(signature.name, "").equals(methods)),
                implementation.klass.fields.stream()
                        .map(field -> field.signature)
                        .filter(signature -> !signature.name.equals(RESULT_KEYWORD)))
                .filter(signature -> signature != null)
                .map(Signature::toJava)
                .distinct();
    }

    @SuppressWarnings("Convert2MethodRef")
    private String generateCall(Program.Call call, List<Program.Binding> bindings) {
        return bindings.stream()
                .filter(binding -> call.isBoundBy(binding))
                .findFirst()
                .map(binding -> {
                    String code = "/* " + binding + " */\n\n";
                    if (call.signature.name.startsWith(ORIGINAL_KEYWORD)) {
                        if (call.isUsedInRequires(PRE_KEYWORD) || call.isUsedInEnsures(PRE_KEYWORD))
                            code += generateDefinedModelMethod(call.getScopedSignature(true, PRE_KEYWORD), binding.implementation) + "\n";
                        if (call.isUsedInRequires(POST_KEYWORD) || call.isUsedInEnsures(POST_KEYWORD))
                            code += generateDefinedModelMethod(call.getScopedSignature(true, POST_KEYWORD), binding.implementation) + "\n";
                    }
                    if (call.isUsedInBody())
                        code += generateDefinedJavaMethod(call.getScopedSignature(false, ""), binding.implementation);
                    return code;
                })
                .orElseGet(() -> {
                    String code = "/* " + call + " */\n\n";
                    if (call.signature.name.startsWith(ORIGINAL_KEYWORD)) {
                        if (call.isUsedInRequires(PRE_KEYWORD) || call.isUsedInEnsures(PRE_KEYWORD))
                            code += generateUndefinedModelMethod(call.getScopedSignature(true, PRE_KEYWORD)) + "\n";
                        if (call.isUsedInRequires(POST_KEYWORD) || call.isUsedInEnsures(POST_KEYWORD))
                            code += generateUndefinedModelMethod(call.getScopedSignature(true, POST_KEYWORD)) + "\n";
                    }
                    return code + generateUndefinedJavaMethod(call.getScopedSignature(false, ""));
                });
    }

    private String generateJavaClass(String className, Function<String, Stream<String>> fields, Stream<String> methods) {
        String _methods = methods.collect(Collectors.joining("\n"));
        String _fields = Stream.concat(fields.apply(_methods), Stream.of("")).collect(Collectors.joining(";\n"));
        return "class " + className + " {" +
                (!_fields.trim().isEmpty() ? "\n/* FIELDS */\n" : "") + _fields +
                (!_methods.trim().isEmpty() ? "\n/* METHODS */\n" : "") + _methods +
                "}";
    }

    String generateJavaClass(Program.Implementation implementation, List<Program.Binding> bindings) {
        return generateJavaClass(implementation.klass.name,
                methods -> generateFields(implementation, methods),
                Stream.concat(
                        implementation.getExtendedCall(bindings).stream().map(call -> generateCall(call, bindings)),
                        Stream.of("/* " + implementation + " */\n\n" + generateConcreteJavaMethod(implementation))))
                .replace(RESULT_KEYWORD + "_" + getBareMethodName(implementation.signature), RESULT_KEYWORD);
    }

    private class Placeholder {
        private final Signature signature;
        private final boolean isModelBehavior;
        private final String R;
        private final String E;

        Placeholder(Signature signature, boolean isAbstract, boolean isModelBehavior) {
            this.signature = signature;
            this.isModelBehavior = isModelBehavior;
            if (isAbstract) {
                String hash = signature.toHash();
                R = "R_" + hash;
                E = "E_" + hash;
            } else
                R = E = null;
        }

        private List<String> getArguments(String requiresDef, String ensuresDef, String assignableDef) {
            ArrayList<String> args = new ArrayList<>();
            if (!isModelBehavior) {
                if (R == null) {
                    if (requiresDef != null) {
                        args.add("requires");
                        args.add(requiresDef + ";");
                    }
                } else {
                    args.add("requires_abs");
                    args.add(R + ";");
                    if (requiresDef != null) {
                        args.add("def");
                        args.add(R + " = " + requiresDef + ";");
                    }
                }
            }
            if (isModelBehavior && ensuresDef != null)
                ensuresDef = "\\result == (" + ensuresDef + ")";
            if (E == null) {
                if (ensuresDef != null) {
                    args.add("ensures");
                    args.add(ensuresDef + ";");
                }
            } else {
                args.add("ensures_abs");
                args.add(E + ";");
                if (ensuresDef != null) {
                    args.add("def");
                    args.add(E + " = " + ensuresDef + ";");
                }
            }
            if (!isModelBehavior && assignableDef != null) {
                args.add("assignable");
                args.add(assignableDef + ";");
            }
            return args;
        }

        String generateNormalBehaviorContract(String requiresDef, String ensuresDef, String assignableDef) {
            List<String> arguments = getArguments(requiresDef, ensuresDef, assignableDef);
            return CodeGenerator.this.generateContract("normal_behavior", arguments.toArray(new String[]{}));
        }

        String generateModelBehaviorContract(String ensuresDef) {
            List<String> arguments = getArguments(null, ensuresDef, null);
            arguments.add("model");
            arguments.add(signature.toJava() + " { return true; }");
            return CodeGenerator.this.generateContract("model_behavior", arguments.toArray(new String[]{}));
        }
    }
}
