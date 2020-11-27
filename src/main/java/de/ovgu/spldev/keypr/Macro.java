package de.ovgu.spldev.keypr;

import java.util.ArrayList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class Macro implements Utils.Dumpable {
    private static final Pattern PATTERN = Pattern.compile("^(.*)\\((.*)\\)$");

    private final String findName;
    private List<String> findParameters;
    private final String replaceTemplate;
    private final boolean isRecursive;

    public Macro(String find, String replace, boolean isRecursive)  {
        Matcher matcher = PATTERN.matcher(find.trim());
        if (matcher.matches()) {
            findName = matcher.group(1).trim();
            this.findParameters = new ArrayList<>();
            findParameters.addAll(Utils.split(matcher.group(2)));
        } else
            findName = find;
        this.replaceTemplate = replace;
        this.isRecursive = isRecursive;
    }

    Macro(String findName, List<String> findParameters, String replaceTemplate, boolean isRecursive) {
        this.findName = findName;
        this.findParameters = findParameters;
        this.replaceTemplate = replaceTemplate;
        this.isRecursive = isRecursive;
    }

    private Pattern getFindPattern() {
        return Pattern.compile(Pattern.quote(findName) + "\\s*\\((.*?)\\)");
    }

    boolean isApplicable(String str) {
        return getFindPattern().matcher(str).find();
    }

    public String apply(String str) {
        if (findParameters == null)
            return str.replace(findName, replaceTemplate);
        Matcher matcher = getFindPattern().matcher(str);
        if (matcher.find()) {
            List<String> findArguments = new ArrayList<>(Utils.split(matcher.group(1)));
            String replaceInstance = replaceTemplate;
            if (findParameters.size() == 1 && findParameters.get(0).startsWith("...")) {
                String replacement = String.join(", ", findArguments);
                if (findParameters.get(0).startsWith("...,") && !replacement.isEmpty())
                    replacement = ", " + replacement;
                replaceInstance = replaceInstance.replace(findParameters.get(0), replacement);
            } else {
                if (findParameters.size() != findArguments.size())
                    throw new RuntimeException("expected " + findParameters.size() + " arguments for " + findName + ", got " + findArguments.size());
                for (int i = 0; i < findParameters.size(); i++)
                    replaceInstance = replaceInstance.replace(findParameters.get(i), findArguments.get(i));
            }
            str = matcher.replaceFirst(Matcher.quoteReplacement(replaceInstance));
            return isRecursive ? apply(str) : str;
        } else
            return str;
    }

    static String applyMacros(String str, List<Macro> macros) {
        for (Macro macro : macros)
            str = macro.apply(str);
        return str;
    }

    static Macro getMethodMacro(String find, String replace, List<String> prependParameters) {
        List<String> findParameters = new ArrayList<>();
        String withSeparator = prependParameters.size() > 0 ? "," : "";
        findParameters.add("..." + withSeparator + "args");
        return new Macro(
                find, findParameters, replace + "(" + String.join(", ", prependParameters) +
                "..." + withSeparator + "args)", true);
    }

    public String toString() {
        if (findParameters == null)
            return String.format("Macro[%s]", findName);
        return String.format("Macro[%s(%s)]", findName, String.join(", ", findParameters));
    }
}
