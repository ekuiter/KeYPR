package de.ovgu.spldev.keypr;

public class Main {
    public static void main(String[] args) {
        if (args.length > 1)
            throw new RuntimeException("invalid usage");
        if (args.length == 0) {
            KeYBridge.runKey(null);
            return;
        }

        ClojureBridge.repl(
                args[0].equals("repl")
                        ? "(clojure.main/repl)"
                        : !args[0].trim().startsWith("(")
                        ? "(load! \"" + args[0].replace("\\", "\\\\") + "\")"
                        : "(println " + args[0] + ")");
    }
}