package Teacher;

import com.google.common.collect.ImmutableList;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.util.Pair;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.SolverContext;

import java.util.*;
import java.util.concurrent.atomic.AtomicInteger;

class DataGenerator {
    private static final AtomicInteger ID = new AtomicInteger(0);
    private static final AtomicInteger posNumber = new AtomicInteger(0);
    private static final AtomicInteger negNumber = new AtomicInteger(0);
    private static boolean modelLabel = true;

    /**
     * generates the initial data set for the Learner
     *
     * @param context    The JavaSMT context containing the formulas
     * @param a,b        The formulas to be interpolated
     * @param commonVars The common variables of the formulas
     * @param size       The size of the entire data set, half positive, half negative
     * @return A Set of unique data points labeled positive and negative
     */
    static Set<List<Number>> getInitialData(SolverContext context,
                                            BooleanFormula a,
                                            BooleanFormula b,
                                            Map<String, Formula> commonVars,
                                            int size) throws NoAssignmentFirstException, NoAssignmentSecondException {
        //get models with assignments for the interpolation formulas
        System.out.println("generating initial data of size " + size);
        System.out.println("Number of positive points: 0");
        System.out.println("Number of negative points: 0");
        modelLabel = true;
        Pair<Boolean, List<Model>> modelAPair = ModelValidator.generateAssignments(context, a, size / 2 + size % 2);
        modelLabel = false;
        Pair<Boolean, List<Model>> modelBPair = ModelValidator.generateAssignments(context, b, size / 2);
        //check, if both formulas were satisfiable
        if (!modelAPair.getFirst()) {
            //first formula unsatisfiable
            System.out.println("Formula A unsatisfiable");
            throw new NoAssignmentFirstException();
        } else if (!modelBPair.getFirst()) {
            //second Formula unsatisfiable
            System.out.println("Formula B unsatisfiable");
            throw new NoAssignmentSecondException();
        } else {
            //only assignments to the common variables are needed for the learning
            Set<List<Number>> pointsA = generatePointsFromModels(modelAPair.getSecond(), commonVars, true);
            Set<List<Number>> pointsB = generatePointsFromModels(modelBPair.getSecond(), commonVars, false);
            Set<List<Number>> data = new HashSet<>(size);
            data.addAll(pointsA);
            data.addAll(pointsB);
            return data;

        }
    }

    /**
     * expands the data set with the assignments found while checking the interpolant conditions
     *
     * @param data       existing data set
     * @param modelsA    list of models with assignments for the first formula
     * @param modelsB    list of models with assignments for the second formula
     * @param commonVars common variables of the formulas
     * @return a larger data set containing the new assignments
     */
    static Set<List<Number>> updateData(Set<List<Number>> data, List<Model> modelsA, List<Model> modelsB, Map<String, Formula> commonVars) {
        System.out.println("updating data");
        //preparing the new set and copying the existing data points
        Set<List<Number>> newData = new HashSet<>(data.size() + modelsA.size() + modelsB.size());
        newData.addAll(data);
        //if assignments for the first formula exist, label them positive and add them
        modelLabel = true;
        Set<List<Number>> pointsA = generatePointsFromModels(modelsA, commonVars, true);
        newData.addAll(pointsA);
        //if assignments for the second formula exist, label them negative and add them
        modelLabel = false;
        Set<List<Number>> pointsB = generatePointsFromModels(modelsB, commonVars, false);
        newData.addAll(pointsB);
        return newData;
    }

    /**
     * Reduces the dimension of the data points by reading only the assignments for the common variables from the models
     *
     * @param models     a list of model containing assignments for one of the formulas
     * @param commonVars the common variables of the interpolation formulas
     * @param label      positive or negative label for the generated points
     * @return a set of ordered lists of assignments to the common variables
     */
    static Set<List<Number>> generatePointsFromModels(List<Model> models, Map<String, Formula> commonVars, boolean label) {
        Set<List<Number>> points = new HashSet<>(models.size());
        for (Model model : models) {
            ImmutableList<Model.ValueAssignment> assignments = model.asList();
            List<Number> point = new ArrayList<>(commonVars.size() + 2);
            //generate unique ID for point
            point.add(ID.incrementAndGet());
            //for each common variable get an assignment from the model
            for (String var : commonVars.keySet()) {
                for (Model.ValueAssignment assignment : assignments) {
                    if (assignment.getName().equals(var)) {
                        if (assignment.getValue() instanceof Boolean) {
                            point.add((Boolean) assignment.getValue() ? 1 : 0);
                        } else {
                            point.add((Number) assignment.getValue());
                        }
                    }
                }

            }
            //add Label
            point.add(label ? 1 : 0);
            points.add(point);
            model.close();
        }
        return points;
    }

    public static void printLabeledModelCount() {
        if (modelLabel) {
            //generated model is positive
            System.out.println("Number of positive points: " + posNumber.incrementAndGet());
        } else {
            //generated model is negative
            System.out.println("Number of negative points: " + negNumber.incrementAndGet());
        }

    }

    static class NoAssignmentFirstException extends Exception {
    }

    static class NoAssignmentSecondException extends Exception {
    }
}
