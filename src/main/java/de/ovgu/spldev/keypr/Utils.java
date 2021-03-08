package de.ovgu.spldev.keypr;

import javax.xml.bind.DatatypeConverter;
import java.io.*;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardCopyOption;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.*;
import java.util.function.Supplier;
import java.util.stream.Collectors;
import java.util.stream.Stream;

public class Utils {
    private static class NullPrintStream extends PrintStream {
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

    static String toHash(String str) {
        try {
            byte[] hash = MessageDigest.getInstance("SHA-1").digest(str.getBytes(StandardCharsets.UTF_8));
            return DatatypeConverter.printHexBinary(hash).substring(0, 16);
        } catch (NoSuchAlgorithmException e) {
            throw new RuntimeException(e);
        }
    }

    static void writeFile(File file, String content) {
        if (content == null)
            return;
        try {
            FileWriter writer = new FileWriter(file);
            writer.write(content);
            writer.close();
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    static void writeFile(Path path, String content) {
        writeFile(path.toFile(), content);
    }

    public static void writeFile(String path, String content) {
        writeFile(Paths.get(path), content);
    }

    static void createDirectory(Path path) {
        try {
            Files.createDirectories(path);
        } catch (IOException e) {
        }
    }

    static void moveDirectory(Path from, Path to) {
        try {
            Files.move(from, to, StandardCopyOption.REPLACE_EXISTING);
        } catch (IOException e) {
        }
    }

    static void deleteDirectory(Path path) {
        try {
            //noinspection ResultOfMethodCallIgnored
            Files.walk(path)
                    .sorted(Comparator.reverseOrder())
                    .map(Path::toFile)
                    .forEach(File::delete);
        } catch (IOException e) {
        }
    }

    public static void deleteDirectoryIfExists(String _path) {
        Path path = Paths.get(_path);
        if (path.toFile().exists())
            Utils.deleteDirectory(path);
    }

    private static String repeat(int n) {
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < n; i++)
            sb.append("  ");
        return sb.toString();
    }

    static String indent(int level) {
        return repeat(level - 1) + "- ";
    }

    static String indentHeading(int level, String heading) {
        return repeat(level - 1) + heading.replaceAll("(.)([A-Z])", "$1 $2").toUpperCase();
    }

    static String join(String... args) {
        return String.join("\n",
                Stream.of(args)
                        .filter(s -> s != null && !s.isEmpty())
                        .toArray(String[]::new));
    }

    static boolean streamEquals(Stream<?> s1, Stream<?> s2) {
        Iterator<?> it1 = s1.iterator(), it2 = s2.iterator();
        while (it1.hasNext() && it2.hasNext())
            if (!it1.next().equals(it2.next()))
                return false;
        return !it1.hasNext() && !it2.hasNext();
    }

    public static class Pair<T, U> implements Dumpable {
        public Pair(T first, U second) {
            this.first = first;
            this.second = second;
        }

        public T first;
        public U second;

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
            return String.format("Pair[%s, %s]", first, second);
        }
    }

    static boolean isDebugLevel() {
        return false;
    }

    static List<String> split(String str) {
        return Arrays.stream(str.trim().split(","))
                .map(String::trim)
                .filter(_str -> !_str.isEmpty())
                .collect(Collectors.toList());
    }

    public interface Dumpable {
        default String dump(int level) {
            return Utils.indent(level) + toString();
        }

        default String dump() {
            return dump(1);
        }
    }

    static String dumpList(List<? extends Dumpable> list, int level) {
        return list.size() > 0
                ? Utils.join(
                list.stream()
                        .map(object -> object.dump(level))
                        .collect(Collectors.joining("\n")))
                : "";
    }
}