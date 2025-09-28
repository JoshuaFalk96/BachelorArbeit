package Teacher;

import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.util.Pair;
import org.sosy_lab.java_smt.api.*;

import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;

class ModelValidator {

    private static final AtomicInteger modelNumber = new AtomicInteger(0);

    /**
     * Checks the learned hypothesis for the conditions of an interpolant, specifically if their negation is satisfiable
     *
     * @param context the JavaSMT context containing the formulas
     * @param a,b     the formulas to be interpolated
     * @param h       the hypothesis from the Learner
     * @return a boolean denoting if h is an interpolant and two models that satisfy the negation of the conditions,
     * if they exist
     */
    static Pair<Boolean, Pair<List<Model>, List<Model>>> validateModel(SolverContext context,
                                                                       BooleanFormula a,
                                                                       BooleanFormula b,
                                                                       BooleanFormula h,
                                                                       int size,
                                                                       boolean runBoth) {
        System.out.println("validate hypothesis");
        BooleanFormulaManager bfmr = context.getFormulaManager().getBooleanFormulaManager();
        //construct the formula a&!h, the negation of condition a -> h
        BooleanFormula ah = bfmr.and(a, bfmr.not(h));
        //construct the formula b&h, the negation of condition !(b&h)
        BooleanFormula bh = bfmr.and(b, h);
        //test condition a -> h
        System.out.println("running first check");
        Pair<Boolean, List<Model>> firstCheck = generateAssignments(context, ah, size);
        if (!runBoth && firstCheck.getFirst()) {
            return new Pair<>(false, new Pair<>(firstCheck.getSecond(), new ArrayList<>(0)));
        }
        System.out.println("running second check");
        Pair<Boolean, List<Model>> secondCheck = generateAssignments(context, bh, size);
        return new Pair<>(!firstCheck.getFirst() && !secondCheck.getFirst(),
                new Pair<>(firstCheck.getSecond(), secondCheck.getSecond()));
    }

    /**
     * checks if the given formula is satisfiable and returns multiple assignments
     *
     * @param context the JavaSMT context containing the variables
     * @param formula the formula to be satisfied
     * @param count   amount of assignments to be generated
     * @return a boolean denoting if the formula is satisfiable and a list of satisfying models, if they exists
     */
    static Pair<Boolean, List<Model>> generateAssignments(SolverContext context, BooleanFormula formula, int count) {
        try (ProverEnvironment prover = context.newProverEnvironment(SolverContext.ProverOptions.GENERATE_MODELS)) {
            BooleanFormulaManager bfmr = context.getFormulaManager().getBooleanFormulaManager();
            boolean solvable = false;
            List<Model> models = new ArrayList<>(count);
            prover.addConstraint(formula);
            for (int i = 0; !prover.isUnsat() && i < count; i++) {
                //the formula can be satisfied
                solvable = true;
                //get one assignment
                Model model = prover.getModel();
                models.add(model);
                //print current number of generated models
                System.out.println("Number of generated models: " + modelNumber.incrementAndGet());
                DataGenerator.printLabeledModelCount();
                //generate formula representing assignment
                final List<BooleanFormula> modelAssignmentsAsFormulas = new ArrayList<>();
                for (Model.ValueAssignment va : model) {
                    modelAssignmentsAsFormulas.add(va.getAssignmentAsFormula());
                }
                //remove assignment from possible solutions
                prover.addConstraint(bfmr.not(bfmr.and(modelAssignmentsAsFormulas)));
            }
            return new Pair<>(solvable, models);
        } catch (InterruptedException | SolverException e) {
            throw new RuntimeException(e);
        }
    }
}
