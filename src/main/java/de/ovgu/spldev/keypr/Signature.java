package de.ovgu.spldev.keypr;

import java.util.*;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

public abstract class Signature {
    private static final String SEPARATOR = "::";

    public String type;
    public String className;
    public String name;

    protected Signature() {
    }

    protected Signature(String type, String className, String name) {
        this.type = type;
        this.className = className;
        this.name = name;
    }

    public abstract String toString();

    abstract String toJava();

    abstract String toHash();

    abstract Signature copy();

    Signature toAbsolute(Signature other) {
        Signature thisCopy = copy();
        thisCopy.className = className.equals("self") || className.equals("this") || className.isEmpty() ? other.className : className;
        return thisCopy;
    }

    Signature asBoolean() {
        Signature thisCopy = copy();
        thisCopy.type = "boolean";
        return thisCopy;
    }

    Signature withName(String name) {
        Signature thisCopy = copy();
        thisCopy.name = name;
        return thisCopy;
    }

    public static class Field extends Signature {
        public Field(String type, String className, String name) {
            super(type, className, name);
        }

        public String toString() {
            return type + " " + (className != null ? className : "") + SEPARATOR + name;
        }

        String toJava() {
            return type + " " + name;
        }

        String toHash() {
            return Utils.toHash(name);
        }

        Signature copy() {
            return new Field(type, className, name);
        }

        public boolean equals(Object o) {
            if (this == o) return true;
            if (!(o instanceof Field)) return false;
            Field field = (Field) o;
            return Objects.equals(type, field.type) &&
                    Objects.equals(className, field.className) &&
                    Objects.equals(name, field.name);
        }

        public int hashCode() {
            return Objects.hash(type, className, name);
        }
    }

    public static class Method extends Signature {
        private static final Pattern PATTERN = Pattern.compile("^(.*)\\s+(.*)" + SEPARATOR + "(.*)\\((.*)\\)$");

        public List<Utils.Pair<String, String>> parameters;

        public Method(String type, String className, String name, List<Utils.Pair<String, String>> parameters) {
            super(type, className, name);
            AtomicInteger paramCounter = new AtomicInteger(1);
            this.parameters = parameters.stream()
                    .map(pair -> new Utils.Pair<>(pair.first,
                            pair.second != null ? pair.second : "_" + paramCounter.getAndIncrement()))
                    .collect(Collectors.toList());
        }

        public Method(String functionSpecification) {
            Matcher matcher = PATTERN.matcher(functionSpecification.trim());
            if (!matcher.find())
                throw new IllegalArgumentException("invalid function specification, expected <type> <class>::<name>(<parameters>)");
            type = matcher.group(1).trim();
            className = matcher.group(2).trim();
            name = matcher.group(3).trim();
            parameters = new ArrayList<>();
            AtomicInteger paramCounter = new AtomicInteger(1);
            Arrays.stream(matcher.group(4).trim().split(","))
                    .map(String::trim)
                    .map(str -> str.split("\\s+"))
                    .forEach(_parts -> {
                        if (String.join("", _parts).isEmpty())
                            return;
                        if (_parts.length == 1) {
                            parameters.add(new Utils.Pair<>(_parts[0], "_" + paramCounter));
                            paramCounter.getAndIncrement();
                        } else if (_parts.length == 2)
                            parameters.add(new Utils.Pair<>(_parts[0], _parts[1]));
                        else
                            throw new IllegalArgumentException("invalid parameters in signature specification");
                    });
        }

        Method prependParameters(List<Utils.Pair<String, String>> parameters) {
            Method thisCopy = (Method) copy();
            thisCopy.parameters = new ArrayList<>(parameters);
            thisCopy.parameters.addAll(this.parameters);
            return thisCopy;
        }

        protected String parametersToJavaString() {
            return parameters != null ? "(" + parameters.stream()
                    .map(entry -> entry.first + (entry.second != null ? " " + entry.second : ""))
                    .collect(Collectors.joining(", ")) + ")" : "";
        }

        protected String parametersToKeyString() {
            return parameters != null ? "(" + parameters.stream()
                    .map(pair -> pair.first)
                    .collect(Collectors.joining(",")) + ")" : "";
        }

        public String toString() {
            return type + " " + (className != null ? className : "") + SEPARATOR + name + parametersToJavaString();
        }

        String toJava() {
            return type + " " + name + parametersToJavaString();
        }

        String toHash() {
            return Utils.toHash(name + parametersToKeyString());
        }

        Method withParameters(Method other) {
            Method thisCopy = (Method) copy();
            thisCopy.parameters = new ArrayList<>(other.parameters);
            return thisCopy;
        }

        boolean matches(Method other) {
            return type.equals(other.type) && className.equals(other.className) && name.equals(other.name) &&
                    Utils.streamEquals(
                            parameters.stream().map(pair -> pair.first),
                            other.parameters.stream().map(pair -> pair.first));
        }

        public boolean equals(Object o) {
            if (this == o) return true;
            if (!(o instanceof Method)) return false;
            Method method = (Method) o;
            return Objects.equals(type, method.type) &&
                    Objects.equals(className, method.className) &&
                    Objects.equals(name, method.name) &&
                    Objects.equals(parameters, method.parameters);
        }

        public int hashCode() {
            return Objects.hash(type, className, name, parameters);
        }

        Signature copy() {
            return new Method(type, className, name, new ArrayList<>(parameters));
        }
    }

    public static class Call {
        public final Method inSignature;
        public final Method toSignature;

        public Call(Method inSignature, Method toSignature) {
            this.inSignature = inSignature;
            this.toSignature = (Method) toSignature.toAbsolute(inSignature);
        }

        public String toString() {
            return inSignature + "." + toSignature;
        }

        public boolean equals(Object o) {
            if (this == o) return true;
            if (!(o instanceof Call)) return false;
            Call call = (Call) o;
            return Objects.equals(inSignature, call.inSignature) &&
                    Objects.equals(toSignature, call.toSignature);
        }

        public int hashCode() {
            return Objects.hash(inSignature, toSignature);
        }
    }
}
