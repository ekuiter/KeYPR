package de.ovgu.spldev.keypr;

import java.io.*;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Comparator;
import java.util.Objects;
import java.util.function.Supplier;

class Utils {
    static class NullPrintStream extends PrintStream {
        NullPrintStream() {
            super(new NullByteArrayOutputStream());
        }

        static class NullByteArrayOutputStream extends ByteArrayOutputStream {
            public void write(int b) {
            }

            public void write(byte[] b, int off, int len) {
            }

            public void writeTo(OutputStream out) {
            }
        }
    }

    static <T> T runSilentAndReturn(Supplier<T> supplier, boolean silentErr) {
        PrintStream oldOut = System.out, oldErr = System.err;
        System.setOut(new NullPrintStream());
        if (silentErr)
            System.setErr(new NullPrintStream());
        try {
            return supplier.get();
        } finally {
            System.setOut(oldOut);
            System.setErr(oldErr);
        }
    }

    static void runSilent(Runnable runnable) {
        runSilentAndReturn(() -> {
            runnable.run();
            return null;
        }, true);
    }

    static void writeFile(Path path, String content) {
        if (content == null)
            return;
        try {
            FileWriter writer = new FileWriter(path.toFile());
            writer.write(content);
            writer.close();
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    static void createDirectory(Path path) {
        try {
            Files.createDirectories(path);
        } catch (IOException ignored) {
        }
    }

    static void deleteDirectory(Path path) {
        try {
            if (path.toFile().exists())
                //noinspection ResultOfMethodCallIgnored
                Files.walk(path)
                        .sorted(Comparator.reverseOrder())
                        .map(Path::toFile)
                        .forEach(File::delete);
        } catch (IOException ignored) {
        }
    }

    public static class Pair<T, U> {
        Pair(T first, U second) {
            this.first = first;
            this.second = second;
        }

        T first;
        U second;

        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;
            Pair<?, ?> pair = (Pair<?, ?>) o;
            return Objects.equals(first, pair.first) &&
                    Objects.equals(second, pair.second);
        }

        public int hashCode() {
            return Objects.hash(first, second);
        }

        public String toString() {
            return String.format("(%s, %s)", first, second);
        }
    }
}