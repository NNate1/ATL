import java.io.File;
import java.io.FileOutputStream;
import java.io.FileWriter;
import java.io.PrintStream;
import java.io.PrintWriter;
import java.nio.file.Paths;
import java.time.LocalDateTime;
import java.time.format.DateTimeFormatter;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Scanner;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.parser.CompUtil;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.TranslateAlloyToKodkod;

public class Checker {

    public static void run(final String fileName, final int numChecks, final A4Options opt, final PrintWriter writer)
            throws Exception {
        final A4Reporter rep = new A4Reporter();
        final var world = CompUtil.parseEverything_fromFile(rep, null, fileName);
        final var commands = world.getAllCommands();

        if (commands.size() == 0) {
            println(writer, "No commands found in the Alloy model.");
            return;
        }

        println(writer, "Check, Average (ms)" + createCSVHeader(numChecks));

        for (final var cmd : commands) {

            final List<Double> times = new ArrayList<>();
            for (int i = 0; i < numChecks; i++) {
                final long startTime = System.nanoTime();
                final var result = TranslateAlloyToKodkod.execute_command(rep, world.getAllReachableSigs(), cmd, opt);
                final long elapsedTime = System.nanoTime() - startTime;

                if (cmd.expects != -1 && cmd.expects == 0 && result.satisfiable()) {
                    // What to do here?

                    String unexpectedMessage = String.format(
                            "Unexpected result for command: %s. Expected: %d, Got: %s",
                            cmd.label, cmd.expects, result.satisfiable());
                    System.err.println(unexpectedMessage);
                    println(writer, unexpectedMessage);
                }
                times.add(elapsedTime / 1_000_000.0); // Convert to milliseconds
            }

            final double average = times.stream().mapToDouble(Double::doubleValue).average().orElse(0.0);

            if (cmd.check) {
                println(writer, "Check " + cmd.label + ", " + average + ", " + formatTimes(times));
            } else {
                println(writer, "Run " + cmd.label + ", " + average + ", " + formatTimes(times));
            }
        }
    }

    private static String createCSVHeader(final int numChecks) {
        final StringBuilder header = new StringBuilder();
        for (int i = 1; i <= numChecks; i++) {
            header.append(", ").append(i).append(" (ms)");
        }
        return header.toString();
    }

    private static String formatTimes(final List<Double> times) {
        final StringBuilder formatted = new StringBuilder();
        for (final double time : times) {
            formatted.append(time).append(",");
        }
        return formatted.toString();
    }

    private static void printHelp() {
        System.out.println("usage: script_dht.py [-h] [-d OUTPUT_DIR] [-n N] -f F [F ...]");
    }

    private static void println(PrintWriter writer, String content) {

        if (writer != null) {
            writer.println(content);
        } else {
            System.out.println(content);
        }
    }

    public static void main(final String[] args) throws Exception {

        int numChecks = 10;
        String outputDir = null;
        List<String> modelFiles = new ArrayList<>();

        for (int i = 0; i < args.length; i++) {
            switch (args[i]) {
                case "-n":
                    numChecks = Integer.parseInt(args[++i]);
                    break;
                case "-d":
                    outputDir = args[++i];
                    break;
                case "-f":
                    for (i = i + 1; i < args.length && !args[i].equals("-n") && !args[i].equals("-d"); i++) {
                        modelFiles.add(args[i]);
                    }
                    --i;
                    break;
                case "-h":
                    printHelp();
                    return;
                default:
                    System.out.println("Unknown flag: " + args[i]);
                    printHelp();
                    return;
            }
        }

        final List<String> files = new ArrayList<>();
        for (final String model : modelFiles) {
            final File file = new File(model.trim());
            if (file.exists()) {
                files.add(file.getAbsolutePath());
                System.out.println("File found: " + model);
            } else {
                System.out.println("File not found: " + model);
            }
        }

        if (files.isEmpty()) {
            System.out.println("No valid model files provided. Exiting.");
            printHelp();
            return;

        }

        final A4Options opt = new A4Options();
        opt.noOverflow = true;

        // Configure solvers

        final A4Options.SatSolver[] solvers = {
                A4Options.SatSolver.MiniSatJNI,
                A4Options.SatSolver.LingelingJNI,
                A4Options.SatSolver.GlucoseJNI,
                A4Options.SatSolver.SAT4J
        };

        File outputDirectory = null;
        if (outputDir != null) {
            outputDirectory = new File(outputDir);
            if (!outputDirectory.exists() && !outputDirectory.mkdirs()) {
                System.out.println("Failed to create output directory: " + outputDir);
                return;
            }
        }

        for (final String fileName : files) {
            System.out.println(fileName);
            for (final var solver : solvers) {
                opt.solver = solver;

                final String baseName = Paths.get(fileName).getFileName().toString();
                if (outputDirectory != null) {

                    String timestamp = LocalDateTime.now().format(DateTimeFormatter.ofPattern("yyyyMMdd_HHmmss"));
                    String baseNameWithoutExtension = baseName.contains(".")
                            ? baseName.substring(0, baseName.lastIndexOf("."))
                            : baseName;

                    File outputFile = new File(outputDirectory,
                            baseNameWithoutExtension + "_" + solver + "_" + timestamp + ".csv");

                    try (PrintWriter writer = new PrintWriter(new FileWriter(outputFile))) {
                        System.out.printf("Processing %s with solver %s... Output: %s%n",
                                baseName, solver, outputFile.getAbsolutePath());
                        run(fileName, numChecks, opt, writer);
                    }
                } else {
                    System.out.printf("\nChecking %s with solver %s", baseName, solver);
                    run(fileName, numChecks, opt, null);

                }
            }
        }
    }
}
