package DeLP_GDPR.delp.reasoner;

import org.tweetyproject.commons.Reasoner;

import org.tweetyproject.commons.Formula;

import DeLP_GDPR.commons.util.rules.Derivation;
import DeLP_GDPR.commons.util.rules.Rule;
import DeLP_GDPR.delp.semantics.ComparisonCriterion;
import DeLP_GDPR.delp.semantics.DelpAnswer;
import DeLP_GDPR.delp.semantics.DialecticalTree;
import DeLP_GDPR.delp.semantics.EmptyCriterion;
import DeLP_GDPR.delp.semantics.DelpAnswer.Type;
import DeLP_GDPR.delp.syntax.DefeasibleLogicProgram;
import DeLP_GDPR.delp.syntax.DefeasibleRule;
import DeLP_GDPR.delp.syntax.DelpArgument;
import DeLP_GDPR.delp.syntax.DelpRule;
import DeLP_GDPR.logics.fol.syntax.FolFormula;

import java.util.ArrayDeque;
import java.util.Collection;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * This reasoner performs default dialectical reasoning on some given DeLP.
 *
 */
public class DelpReasoner implements Reasoner<DelpAnswer.Type, DefeasibleLogicProgram, FolFormula> {
    private ComparisonCriterion comparisonCriterion = new EmptyCriterion();
    static HashMap<Formula, Set<Derivation<DelpRule>>> derivations_hashmap = new HashMap<Formula, Set<Derivation<DelpRule>>>();
    
    // Counter for the number of trees
    private int treeCount = 0;
 // Counter for the number of trees
  
    
    // Variable to track the total depth
    private int totalDepth = 0;

    public DelpReasoner(ComparisonCriterion comparisonCriterion) {
        this.comparisonCriterion = comparisonCriterion;
    }

    public ComparisonCriterion getComparisonCriterion() {
        return comparisonCriterion;
    }

    public Set<DelpArgument> getWarrants(DefeasibleLogicProgram delp) {
        DefeasibleLogicProgram groundDelp = delp.ground();
        Set<DelpArgument> all_arguments = groundDelp.ground().getArguments();
        return all_arguments.stream().filter(argument -> isWarrant(groundDelp, argument)).collect(Collectors.toSet());
    }

    private boolean isWarrant(DefeasibleLogicProgram groundDelp, DelpArgument argument) {
        DialecticalTree dtree = new DialecticalTree(argument);
        Deque<DialecticalTree> stack = new ArrayDeque<>();
        stack.add(dtree);
        while (!stack.isEmpty()) {
            DialecticalTree dtree2 = stack.pop();
            stack.addAll(dtree2.getDefeaters(groundDelp, comparisonCriterion));
        }
        return dtree.getMarking().equals(DialecticalTree.Mark.UNDEFEATED);
    }

    public static Set<DelpArgument> getArgumentsWithConclusion(DefeasibleLogicProgram delp, FolFormula f) {
        Collection<DelpRule> allRules = new HashSet<DelpRule>();
        allRules.addAll(delp);
        Set<Derivation<DelpRule>> allDerivations;
        if (derivations_hashmap.containsKey(f)) {
            allDerivations = derivations_hashmap.get(f);
        } else {
            allDerivations = Derivation.allDerivations(allRules, f);
            derivations_hashmap.put(f, allDerivations);
        }
        Set<DelpArgument> arguments = new HashSet<>();

        for (Derivation<DelpRule> derivation : allDerivations) {
            Set<DefeasibleRule> rules = derivation.stream().filter(rule -> rule instanceof DefeasibleRule)
                    .map(rule -> (DefeasibleRule) rule).collect(Collectors.toSet());
            if (delp.isConsistent(rules))
                arguments.add(new DelpArgument(rules, (FolFormula) derivation.getConclusion()));
        }

        Set<DelpArgument> result = new HashSet<>();
        for (DelpArgument argument1 : arguments) {
            boolean is_minimal = true;
            for (DelpArgument argument2 : arguments) {
                if (argument1.getConclusion().equals(argument2.getConclusion())
                        && argument2.isStrongSubargumentOf(argument1)) {
                    is_minimal = false;
                    break;
                }
            }
            if (is_minimal)
                result.add(argument1);
        }
        return result;
    }

    @Override
    public Type query(DefeasibleLogicProgram delp, FolFormula f) {
        DialecticalTree dtree = null;
        boolean warrant = false;
        Set<DelpArgument> args = getArgumentsWithConclusion(delp.ground(), f);

        for (DelpArgument arg : args) {
            dtree = new DialecticalTree(arg);
            Deque<DialecticalTree> stack = new ArrayDeque<>();
            stack.add(dtree);
            treeCount++;
            while (!stack.isEmpty()) {
                DialecticalTree dtree2 = stack.pop();
                stack.addAll(dtree2.getDefeaters(delp.ground(), comparisonCriterion));
            }
            System.out.println("Dialectic tree depth: " + dtree.getDepth());
            if (dtree.getMarking().equals(DialecticalTree.Mark.UNDEFEATED)) {
                warrant = true;
            }
        }

        boolean comp_warrant = false;
        if (!warrant) {
            args = getArgumentsWithConclusion(delp.ground(), (FolFormula) f.complement());
            for (DelpArgument arg : args) {
                dtree = new DialecticalTree(arg);
                Deque<DialecticalTree> stack = new ArrayDeque<>();
                stack.add(dtree);
                while (!stack.isEmpty()) {
                    DialecticalTree dtree2 = stack.pop();
                    stack.addAll(dtree2.getDefeaters(delp.ground(), comparisonCriterion));
                }
                System.out.println("Dialectic tree supporting the complement of the query, depth: " + dtree.getDepth() + ":\n " + dtree);
                comp_warrant = dtree.getMarking().equals(DialecticalTree.Mark.UNDEFEATED);
            }
            System.out.println("Number of trees generated: " + treeCount);
        }

        if (warrant) {
            System.out.println("Dialectic tree supporting query, depth: " + dtree.getDepth() + ":\n " + dtree);
            return Type.YES;
        } else if (comp_warrant) {
            return Type.NO;
        } else {
            return Type.UNDECIDED;
        }
    }

    public boolean isInstalled() {
        return true;
    }

    public int getTreeCount() {
        return treeCount;
    }
}