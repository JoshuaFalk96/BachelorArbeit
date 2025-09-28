package Teacher;

import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.util.Pair;
import org.apache.commons.cli.*;
import org.jetbrains.annotations.NotNull;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.api.*;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;

import java.io.FileWriter;
import java.io.IOException;
import java.nio.file.Path;
import java.util.*;

import static java.nio.file.Files.readAllBytes;

public class Wrapper {
    public static void main(String[] args) {
        //parse command line arguments
        Options options = defineCommandLineOptions();
        CommandLine cmd;
        CommandLineParser parser = new DefaultParser();
        HelpFormatter helper = new HelpFormatter();
        try {
            cmd = parser.parse(options, args);
            try (SolverContext context = SolverContextFactory.createSolverContext(parseSolver(cmd))) {
                if (cmd.hasOption("so")) {
                    //only split formulas
                    System.out.println("only splitting formulas");
                    generateSplit(context, cmd);
                } else {
                    //run interpolation
                    System.out.println("running interpolation");
                    TeacherController controller = buildController(context, cmd);
                    BooleanFormula interpolant = controller.interpolate();
                    System.out.println("Learned Interpolant :" + interpolant);
                }
            } catch (InvalidConfigurationException e) {
                throw new RuntimeException(e);
            }
        } catch (ParseException e) {
            System.out.println(e.getMessage());
            helper.printHelp("Usage:", options);
            System.exit(1);
        }

    }

    private static void generateSplit(SolverContext context, CommandLine cmd) throws ParseException {
        try {
            Pair<BooleanFormula, BooleanFormula> formulaPair = parseFormulas(context, cmd);
            FormulaManager fmgr = context.getFormulaManager();
            String outputPath = cmd.getOptionValue("o", "../output");
            String formulaName = Path.of(cmd.getOptionValue("fs")).getFileName().toString();
            try (FileWriter fileWriter = new FileWriter(outputPath + "/first_formula_" + formulaName)) {
                fileWriter.write(fmgr.dumpFormula(formulaPair.getFirst()).toString());
            }
            try (FileWriter fileWriter = new FileWriter(outputPath + "/second_formula_" + formulaName)) {
                fileWriter.write(fmgr.dumpFormula(formulaPair.getSecond()).toString());
            }
        } catch (SolverException | InterruptedException |
                 FormulaHandler.NoSplitException | IOException e) {
            throw new RuntimeException(e);
        }
    }

    private static TeacherController buildController(SolverContext context, CommandLine cmd) throws ParseException {
        try {
            Pair<BooleanFormula, BooleanFormula> formulaPair = parseFormulas(context, cmd);
            return new TeacherController(context,
                    formulaPair.getFirst(),
                    formulaPair.getSecond(),
                    cmd.getOptionValue("lenv", "../MIGML_Learner/sklearn/venvSKlearn/Scripts/python.exe"),
                    cmd.getOptionValue("lexe", "../MIGML_Learner/sklearn/learning/learn_invariant.py"),
                    cmd.getOptionValue("o", "../output"),
                    Integer.parseInt(cmd.getOptionValue("si", "2")),
                    Integer.parseInt(cmd.getOptionValue("sd", "1")),
                    cmd.hasOption("rb"),
                    cmd.getOptionValue("l", "haltermann"));
        } catch (FormulaHandler.NoSplitException | InterruptedException |
                 SolverException e) {
            throw new RuntimeException(e);
        }
    }

    private static Pair<BooleanFormula, BooleanFormula> parseFormulas(SolverContext context, CommandLine cmd)
            throws ParseException, SolverException, InterruptedException, FormulaHandler.NoSplitException {
        BooleanFormula firstFormula;
        BooleanFormula secondFormula;
        if (cmd.hasOption("fs")) {
            //single formula input
            //split formula
            System.out.println("running with single formula");
            BooleanFormula formula = FormulaHandler.getFormula(context, cmd.getOptionValue("fs"));
            Pair<BooleanFormula, BooleanFormula> formulaSplit = FormulaHandler.splitFormula(context,
                    context.getFormulaManager().getBooleanFormulaManager(), formula);
            firstFormula = formulaSplit.getFirst();
            secondFormula = formulaSplit.getSecond();
        } else if (cmd.hasOption("f1") && cmd.hasOption("f2")) {
            //two formula input
            System.out.println("running with separate formulas");
            firstFormula = FormulaHandler.getFormula(context, cmd.getOptionValue("f1"));
            secondFormula = FormulaHandler.getFormula(context, cmd.getOptionValue("f2"));
            //Determine and print amount of sub formulas
            BooleanFormulaManager bfmr = context.getFormulaManager().getBooleanFormulaManager();
            Set<BooleanFormula> conjunctionFormulasA = bfmr.toConjunctionArgs(firstFormula, false);
            Set<BooleanFormula> conjunctionFormulasB = bfmr.toConjunctionArgs(secondFormula, false);
            int formulasNumber = (conjunctionFormulasA.size() + conjunctionFormulasB.size());
            System.out.println("Overall formula size: " + formulasNumber);
            System.out.println("First formula size: " + conjunctionFormulasA.size());
            System.out.println("Second formula size: " + conjunctionFormulasB.size());
        } else {
            throw new ParseException("Input formulas not correctly specified");
        }
        return new Pair<>(firstFormula, secondFormula);
    }

    @NotNull
    private static SolverContextFactory.Solvers parseSolver(CommandLine cmd) throws ParseException {
        String solverOption = cmd.getOptionValue("smt", "smtinterpol");
        System.out.println("using solver " + solverOption);
        return switch (solverOption) {
            case "boolector" -> SolverContextFactory.Solvers.BOOLECTOR;
            case "cvc4" -> SolverContextFactory.Solvers.CVC4;
            case "cvc5" -> SolverContextFactory.Solvers.CVC5;
            case "mathsat5" -> SolverContextFactory.Solvers.MATHSAT5;
            case "opensmt" -> SolverContextFactory.Solvers.OPENSMT;
            case "princess" -> SolverContextFactory.Solvers.PRINCESS;
            case "smtinterpol" -> SolverContextFactory.Solvers.SMTINTERPOL;
            case "yices2" -> SolverContextFactory.Solvers.YICES2;
            case "z3" -> SolverContextFactory.Solvers.Z3;
            default -> throw new ParseException("Invalid argument for SMT solver");
        };
    }

    private static Options defineCommandLineOptions() {
        Options options = new Options();
        //define options
        Option formulaSingle = Option.builder("fs")
                .longOpt("formula-single")
                .argName("interpolation formula single")
                .hasArg()
                .desc("""
                        Path to SMT-LIBv2 file of single formula to be interpolated\s
                        formula gets split into two satisfiable formulas""")
                .build();
        options.addOption(formulaSingle);

        Option formulaFirst = Option.builder("f1")
                .longOpt("formula-first")
                .argName("interpolation formula first")
                .hasArg()
                .desc("""
                        Path to SMT-LIBv2 file of first formula to be interpolated\s
                        needs second formula""")
                .build();
        options.addOption(formulaFirst);

        Option formulaSecond = Option.builder("f2")
                .longOpt("formula-second")
                .argName("interpolation formula first")
                .hasArg()
                .desc("""
                        Path to SMT-LIBv2 file of second formula to be interpolated\s
                        needs first formula""")
                .build();
        options.addOption(formulaSecond);

        Option learnerPath = Option.builder("lenv")
                .longOpt("learner-environment")
                .argName("python environment MIGml Learner")
                .hasArg()
                .desc("Path to the virtual python environment for the MIGml Learner")
                .build();
        options.addOption(learnerPath);

        Option learnerExec = Option.builder("lexe")
                .longOpt("learner-executable")
                .argName("executable MIGml Learner")
                .hasArg()
                .desc("Path to the executable of the MIGml Learner")
                .build();
        options.addOption(learnerExec);

        Option learner = Option.builder("l")
                .longOpt("learner")
                .argName("specific MIGml Learner")
                .hasArg()
                .desc("""
                        Which Learner implemented in MIGml should be used\s
                        valid options:\s
                        zhu18\s
                        krishna15\s
                        sharma12\s
                        haltermann""")
                .build();
        options.addOption(learner);

        Option output = Option.builder("o")
                .longOpt("output-path")
                .argName("output directory")
                .hasArg()
                .desc("Path to the output directory for data set and interpolant")
                .build();
        options.addOption(output);

        Option initSize = Option.builder("si")
                .longOpt("size-initial")
                .argName("initial data set size")
                .hasArg()
                .type(Integer.class)
                .desc("Size of the initial data set, half positive, half negative")
                .build();
        options.addOption(initSize);

        Option updateSize = Option.builder("sd")
                .longOpt("size-update")
                .argName("update data size")
                .hasArg()
                .type(Integer.class)
                .desc("Number of additional data points per failed check")
                .build();
        options.addOption(updateSize);

        Option runBoth = Option.builder("rb")
                .longOpt("run-both")
                .argName("run both checks")
                .desc("""
                        true: run both checks on each iteration\s
                        false: start new iteration as soon as first check fails""")
                .build();
        options.addOption(runBoth);

        Option solver = Option.builder("smt")
                .longOpt("smt-solver")
                .argName("used SMT solver")
                .hasArg()
                .desc("""
                        Which SMT solver from JavaSMT for finding assignments\s
                        valid options:\s
                        boolector\s
                        cvc4\s
                        cvc5\s
                        mathsat5\s
                        opensmt\s
                        princess\s
                        smtinterpol\s
                        yices2\s
                        z3""")
                .build();
        options.addOption(solver);

        Option splitOnly = Option.builder("so")
                .longOpt("split-only")
                .argName("only split formula")
                .desc("""
                        true: only splits formula does not run interpolation\s
                        false: run interpolation as normal\s
                        only works with formula-single argument""")
                .build();
        options.addOption(splitOnly);
        return options;
    }
}
