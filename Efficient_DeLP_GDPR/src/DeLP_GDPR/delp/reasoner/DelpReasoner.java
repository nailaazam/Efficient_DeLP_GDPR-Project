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
import java.util.logging.FileHandler;
import java.util.logging.Formatter;
import java.util.logging.Handler;
import java.util.logging.LogRecord;
import java.util.logging.SimpleFormatter;
import java.util.logging.Logger;
import java.util.Scanner;
import java.util.*;
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
          //  logger.log(Level.INFO, "Marking of node: {0}", currentTree.getMarking());
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
    public DelpAnswer.Type query(DefeasibleLogicProgram delp, FolFormula queryFormula) {
        // Ground the program and prepare for evaluation
        DefeasibleLogicProgram groundedDelp = delp.ground();
        Set<DelpArgument> conflictingArguments = new HashSet<>();

        // Original evaluation without considering priorities
        boolean warrant = evaluateArguments(groundedDelp, getArgumentsWithConclusion(groundedDelp, queryFormula), conflictingArguments);
        boolean compWarrant = evaluateArguments(groundedDelp, getArgumentsWithConclusion(groundedDelp, (FolFormula) queryFormula.complement()), conflictingArguments);

        if (!warrant && !compWarrant && !conflictingArguments.isEmpty()) {
            printConflictingArguments(conflictingArguments);
            HashMap<DelpArgument, Integer> priorities = askForPriorities(conflictingArguments);

            Set<DelpArgument> highPriorityArguments = filterByHighestPriority(priorities);
            // Assuming only one highest priority argument is considered
            DelpArgument highestPriorityArgument = highPriorityArguments.iterator().next();

            // Correctly pass the highest priority argument and the priorities map to reevaluateWithPriority
            reevaluateWithPriority(groundedDelp, highestPriorityArgument, queryFormula, priorities);
            
        }

        // Original decision logic if not undecided or priorities do not affect the outcome
        if (warrant && !compWarrant) {
            return DelpAnswer.Type.YES;
        } else if (!warrant && compWarrant) {
            return DelpAnswer.Type.NO;
        } else {
            return DelpAnswer.Type.UNDECIDED;
        }
        }
    private Set<DelpArgument> filterByHighestPriority(HashMap<DelpArgument, Integer> priorities) {
        // Find the minimum priority value
        int minPriority = Collections.min(priorities.values());
        System.out.println("Minimum Priority Value: " + minPriority); // Log the minimum priority value

        // Filter arguments to include only those with the highest priority
        Set<DelpArgument> highPriorityArguments = priorities.entrySet().stream()
                .filter(entry -> entry.getValue() == minPriority)
                .peek(entry -> System.out.println("Filtering Argument: " + entry.getKey() + " with Priority: " + entry.getValue())) // Log each argument being considered
                .map(Map.Entry::getKey)
                .collect(Collectors.toSet());

        // Log the filtered arguments for verification
        System.out.println("Filtered High Priority Arguments: ");
        highPriorityArguments.forEach(arg -> System.out.println(arg));

        return highPriorityArguments;
    }
 
    private boolean reevaluateWithPriority(DefeasibleLogicProgram delp, DelpArgument highestPriorityArgument, FolFormula formula, HashMap<DelpArgument, Integer> priorities) {
        System.out.println("Reevaluating with the highest priority argument for formula: " + formula);

        // Directly check if the argument supports or opposes the query
        boolean directlySupports = highestPriorityArgument.getConclusion().equals(formula);
        boolean directlyOpposes = highestPriorityArgument.getConclusion().equals(formula.complement());

        // Log the direct relation of the argument
        if (directlySupports) {
            System.out.println("Result: YES");
        } else if (directlyOpposes) {
            System.out.println("Result: NO");
        }

       // System.out.println("The reevaluation with the highest priority argument remains inconclusive.");
        return false;
    }
    
    private HashMap<DelpArgument, Integer> askForPriorities(Set<DelpArgument> conflictingArguments) {
        HashMap<DelpArgument, Integer> priorities = new HashMap<>();
        Scanner scanner = new Scanner(System.in);
        System.out.println("Assign priorities to the following arguments (lower number means higher priority):");

        int counter = 1;
        for (DelpArgument argument : conflictingArguments) {
            System.out.println("Argument " + counter + ": " + argument);
            System.out.print("Priority: ");
            int priority = scanner.nextInt();
            priorities.put(argument, priority);
            counter++;
        }

        scanner.close(); // Be cautious about closing the scanner.
        return priorities;
    }

    
    private void printConflictingArguments(Set<DelpArgument> conflictingArguments) {
        System.out.println("Conflicting Arguments:");
        if (conflictingArguments.isEmpty()) {
            System.out.println("No conflicting arguments were found.");
        } else {
            int argumentCounter = 1; // Initialize the counter for numbering arguments
            for (DelpArgument arg : conflictingArguments) {
                System.out.println("Argument " + argumentCounter + ": "); // Use the counter in the output
                //System.out.println("Support (Set of Defeasible Rules):");
                arg.getSupport().forEach(rule -> {
                    System.out.println("\tRule: " + rule);
                    // If DefeasibleRule class has a specific toString implementation, it will be used here.
                });
                System.out.println("Conclusion: " + arg.getConclusion());
                
                System.out.println("---");
                argumentCounter++; // Increment the counter for the next argument
            }
        }
    }
    
    private boolean evaluateArguments(DefeasibleLogicProgram delp, Set<DelpArgument> arguments, Set<DelpArgument> conflictingArguments) {
        boolean foundSupport = false;
        for (DelpArgument argument : arguments) {
            DialecticalTree tree = new DialecticalTree(argument);
            if (evaluateTree(tree, delp, conflictingArguments)) {
                foundSupport = true; // Argument supports the query
            }
        }
        return foundSupport;
    }

    private boolean evaluateTree(DialecticalTree tree, DefeasibleLogicProgram delp, Set<DelpArgument> conflictingArguments) {
        // the delp is the grounded version
        
        DefeasibleLogicProgram groundedDelp = delp.ground();
        Deque<DialecticalTree> stack = new ArrayDeque<>();
        stack.push(tree);

        //int nodeCounter = 0; // Initialize the counter

        while (!stack.isEmpty()) {
            DialecticalTree currentTree = stack.pop();
           // nodeCounter++; // Increment the counter as we're about to process a new node
            System.out.println("Processing node: " + currentTree.getArgument().toString()); // Use the counter in the output
            Set<DialecticalTree> defeaters = currentTree.getDefeaters(groundedDelp, comparisonCriterion);
            for (DialecticalTree defeater : defeaters) {
                System.out.println("Defeater found: " + defeater.getArgument().toString());
                if (defeater.getMarking() == DialecticalTree.Mark.UNDEFEATED) {
                    conflictingArguments.add(defeater.getArgument());
                  //  System.out.println("argument: " + defeater.getArgument().toString());
                } else {
                    stack.push(defeater);
                }
            }
        }
        return conflictingArguments.isEmpty();
    }
    public boolean isInstalled() {
        return true;
    }

    public int getTreeCount() {
        return treeCount;
    }
}