package Teacher;

import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.util.Pair;
import org.sosy_lab.java_smt.api.*;

import java.io.IOException;
import java.nio.file.Path;
import java.util.*;

import static java.nio.file.Files.readAllBytes;

public class FormulaHandler {
    static BooleanFormula getFormula(SolverContext context, String formulaPath) {
        try {
            //read formula
            String formulaString = new String(readAllBytes(Path.of(formulaPath)));
            //parse to JavaSMT
            return context.getFormulaManager().parse(formulaString);
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    static Pair<BooleanFormula, BooleanFormula> splitFormula(SolverContext context,
                                                             BooleanFormulaManager bfmr,
                                                             BooleanFormula unsatFormula)
            throws InterruptedException, SolverException, NoSplitException {
        //split on each 'and'
        System.out.println("splitting formulas");
        Set<BooleanFormula> conjunctionFormulas = bfmr.toConjunctionArgs(unsatFormula, false);
        BooleanFormula a;
        BooleanFormula b;
        if (conjunctionFormulas.size() < 2) {
            //no 'and' in formula to split
            BooleanFormula nnfFormula = context.getFormulaManager().applyTactic(unsatFormula, Tactic.NNF);
            conjunctionFormulas = bfmr.toConjunctionArgs(nnfFormula, false);
            if (conjunctionFormulas.size() < 2) {
                //no 'and' in negative normal form
                throw new NoSplitException("abort: no split possible");
            }
        }
        //split set of formulas in two equal parts
        Spliterator<BooleanFormula> split1 = conjunctionFormulas.spliterator();
        Spliterator<BooleanFormula> split2 = split1.trySplit();

        List<BooleanFormula> formulasA = new ArrayList<>();
        List<BooleanFormula> formulasB = new ArrayList<>();
        //collect Formulas from each split
        split1.forEachRemaining(formulasA::add);
        split2.forEachRemaining(formulasB::add);
        //combine formulas in each split
        a = bfmr.and(formulasA);
        b = bfmr.and(formulasB);
        ProverEnvironment prover = context.newProverEnvironment();
        if (prover.isUnsatWithAssumptions(Collections.singleton(a))) {
            //first formula unsat
            //split first formula
            System.out.println("first formulas unsat, move split left");
            Pair<BooleanFormula, BooleanFormula> split = splitFormula(context, bfmr, a);
            a = split.getFirst();
            b = bfmr.and(split.getSecond(), b);
        }
        if (prover.isUnsatWithAssumptions(Collections.singleton(b))) {
            //second formula unsat
            //split second formula
            System.out.println("second formula unsat, move split right");
            Pair<BooleanFormula, BooleanFormula> split = splitFormula(context, bfmr, b);
            a = bfmr.and(a, split.getFirst());
            b = split.getSecond();
        }
        System.out.println("Overall formula size: " + conjunctionFormulas.size());
        System.out.println("First formula size: " + formulasA.size());
        System.out.println("Second formula size: " + formulasB.size());
        return new Pair<>(a, b);
    }

    static Pair<BooleanFormula, BooleanFormula> getSimpleExample(SolverContext context) {
        BooleanFormulaManager bfmr = context.getFormulaManager().getBooleanFormulaManager();
        IntegerFormulaManager ifmr = context.getFormulaManager().getIntegerFormulaManager();
        NumeralFormula.IntegerFormula x = ifmr.makeVariable("x");
        NumeralFormula.IntegerFormula y = ifmr.makeVariable("y");
        BooleanFormula a1 = ifmr.lessThan(x, ifmr.makeNumber(0));
        BooleanFormula a2 = ifmr.greaterThan(y, ifmr.makeNumber(3));
        BooleanFormula b1 = ifmr.greaterThan(x, ifmr.makeNumber(0));
        BooleanFormula b2 = ifmr.greaterThan(y, ifmr.makeNumber(7));
        BooleanFormula a = bfmr.and(a1, a2);
        BooleanFormula b = bfmr.and(b1, b2);
        return new Pair<>(a, b);
    }

    static class NoSplitException extends Exception {
        public NoSplitException(String s) {
            super(s);
        }
    }
}
