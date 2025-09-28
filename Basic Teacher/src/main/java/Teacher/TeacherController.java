package Teacher;

import com.google.common.collect.ImmutableMap;
import com.google.common.collect.Lists;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.util.Pair;
import org.apache.commons.csv.CSVFormat;
import org.apache.commons.csv.CSVPrinter;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.api.*;

import java.io.BufferedReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.*;

import static java.nio.file.Files.readAllBytes;


public class TeacherController {
    private final SolverContext context;
    private final BooleanFormula A;
    private final BooleanFormula B;
    private final Map<String, Formula> commonVars;
    private final String learnerEnv;
    private final String learnerExec;
    private final String outputPath;
    private final int initialDataSize;
    private final int updateDataSize;
    private final boolean runBothChecks;
    private final String learner;
    private int iterations = 0;

    /**
     * @param firstFormula,secondFormula the formulas that will be interpolated
     * @param context                    the JavaSMT context containing the formulas
     * @param outputPath                 the relative path for the learner communication
     * @param initialDataSize            the size of the initial data set
     * @param updateDataSize             the amount of assignments for each failed check
     * @param runBothChecks              always run both checks or iterate on first failed check
     * @param learner
     */
    public TeacherController(SolverContext context,
                             BooleanFormula firstFormula,
                             BooleanFormula secondFormula,
                             String learnerEnv,
                             String learnerExec,
                             String outputPath,
                             int initialDataSize,
                             int updateDataSize,
                             boolean runBothChecks,
                             String learner) {
        this.context = context;
        this.A = firstFormula;
        this.B = secondFormula;
        this.learnerEnv = learnerEnv;
        this.learnerExec = learnerExec;
        this.outputPath = outputPath;
        this.initialDataSize = initialDataSize;
        this.updateDataSize = updateDataSize;
        this.runBothChecks = runBothChecks;
        this.learner = learner;
        this.commonVars = calculateCommonVars();
    }

    /**
     * Generates the interpolant of the saved formulas iterating through different learned hypothesis
     *
     * @return a valid interpolant of the saved formulas
     */
    public BooleanFormula interpolate() {
        //print config
        System.out.println("Size of initial data set: " + initialDataSize);
        System.out.println("Number of data per iteration: " + updateDataSize);
        //generate the initial data set
        Set<List<Number>> data;
        try {
            data = DataGenerator.getInitialData(context, A, B, commonVars, initialDataSize);
        } catch (DataGenerator.NoAssignmentFirstException e) {
            //first formula unsatisfiable
            System.out.println("First Formula unsatisfiable return trivial interpolant \"False\"");
            return context.getFormulaManager().getBooleanFormulaManager().makeFalse();
        } catch (DataGenerator.NoAssignmentSecondException e) {
            //second formula unsatisfiable
            System.out.println("Second Formula unsatisfiable return trivial interpolant \"True\"");
            return context.getFormulaManager().getBooleanFormulaManager().makeTrue();
        }
        //run the learning loop
        while (true) {
            //print number of iterations
            System.out.println("Number of iterations: " + ++iterations);
            //get hypothesis h from Learner
            BooleanFormula h = learnerCall(data);
            //check if hypothesis is interpolant
            Pair<Boolean, Pair<List<Model>, List<Model>>> validationResult = ModelValidator.validateModel(
                    context, A, B, h, updateDataSize, runBothChecks);
            if (validationResult.getFirst()) {
                System.out.println("valid interpolant");
                System.out.println(h);
                //return valid interpolant
                return h;
            } else {
                //interpolant is invalid, data gets expanded for new learning attempt
                System.out.println("invalid interpolant");
                System.out.println(h);
                data = DataGenerator.updateData(data,
                        validationResult.getSecond().getFirst(),
                        validationResult.getSecond().getSecond(),
                        commonVars);
            }
        }
    }

    /**
     * calculates a HashMap of the common variables of the saved formulas
     * with their names as keys and the JavaSMT formulas as values
     *
     * @return a HashMap containing the common variables
     */
    private Map<String, Formula> calculateCommonVars() {
        try (SolverContext varContext = SolverContextFactory.createSolverContext(SolverContextFactory.Solvers.SMTINTERPOL)) {
        FormulaManager manager = context.getFormulaManager();
        FormulaManager varManager = varContext.getFormulaManager();
        Map<String, Formula> commonVars = new HashMap<>();
        //get all variables of the formulas
        ImmutableMap<String, Formula> varsA = varManager.extractVariables(varManager.translateFrom(A, manager));
        ImmutableMap<String, Formula> varsB = varManager.extractVariables(varManager.translateFrom(B, manager));
        //compare the variables of both formulas and save the matches
        for (String var : varsA.keySet()) {
            if (varsB.containsKey(var)) commonVars.put(var, varsB.get(var));
        }
        //print variables
        System.out.println("Variables first formula:" + varsA);
        System.out.println("Variables second formula:" + varsB);
        System.out.println("Common Variables: " + commonVars);
        //print number of variables
        int varsCount= varsA.size() + varsB.size() - commonVars.size();
        System.out.println("Number of all variables: " + varsCount);
        System.out.println("Number of variables first formula: " + varsA.size());
        System.out.println("Number of variables second formula: " + varsB.size());
        System.out.println("Number of common variables: " + commonVars.size());
        return commonVars;
        } catch (InvalidConfigurationException e) {
            throw new RuntimeException(e);
        }
    }

    /**
     * Sends the data points to the Learner and waits for a result
     * Writes the data points to a file and evokes the Learner
     * Expects a SMT-LIB formula as result and parses it to JavaSMT
     *
     * @return the hypothesis of the learner converted to JavaSMT
     */
    private BooleanFormula learnerCall(Set<List<Number>> data) {
        String outputData = outputPath + "/learningData.csv";
        System.out.println("calling Learner");
        try (CSVPrinter csvPrinter = new CSVPrinter(new FileWriter(outputData), CSVFormat.DEFAULT)) {
            //write csv file
            csvPrinter.print("ID");
            csvPrinter.printRecord(commonVars.keySet());
            csvPrinter.printRecords(data);
            csvPrinter.flush();
            //define command line for Learner
            List<String> cmd = Lists.newArrayList(learnerEnv,
                    learnerExec,
                    "-d",
                    outputData,
                    "-l",
                    "0",
                    "-t",
                    outputPath + "/hypothesis.smt");
            if (!learner.equals("haltermann")) {
                cmd.add("--" + learner);
            }
            ProcessBuilder pb = new ProcessBuilder(cmd);
            //print Learner output
            //pb.redirectErrorStream(true);
            Process learner = pb.start();
//            final BufferedReader readerOut = new BufferedReader(new InputStreamReader(learner.getInputStream()));
//            StringJoiner sj = new StringJoiner(System.lineSeparator());
//            readerOut.lines().iterator().forEachRemaining(p -> sj.add("		" + p));
//            System.out.println(sj.toString());
            //run and wait for Learner
            int waitFor = learner.waitFor();
            //System.out.println(waitFor);
            //parse output from Learner
            String hypothesis = new String(readAllBytes(Path.of(outputPath + "/hypothesis.smt")));
            return context.getFormulaManager().parse(hypothesis);
        } catch (IOException | InterruptedException e) {
            throw new RuntimeException(e);
        }
    }
}
