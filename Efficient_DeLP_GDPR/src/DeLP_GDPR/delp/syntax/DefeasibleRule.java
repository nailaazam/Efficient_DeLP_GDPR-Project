package DeLP_GDPR.delp.syntax;

import DeLP_GDPR.logics.commons.syntax.RelationalFormula;
import DeLP_GDPR.logics.commons.syntax.interfaces.Term;
import DeLP_GDPR.logics.fol.syntax.FolFormula;

import java.util.Set;
import java.util.stream.Collectors;

/**
 * This class models a defeasible rule in defeasible logic programming.
 */
public class DefeasibleRule extends DelpRule {

    private int priority; // Priority of the defeasible rule

    /**
     * Initializes the defeasible rule with the given parameters
     *
     * @param head a literal
     * @param body a set of literals
     */
    public DefeasibleRule(FolFormula head, Set<FolFormula> body) {
        this(head, body, 0); // Default priority is set to 0
    }

    /**
     * Initializes the defeasible rule with the given parameters
     *
     * @param head     a literal
     * @param body     a set of literals
     * @param priority priority of the rule
     */
    public DefeasibleRule(FolFormula head, Set<FolFormula> body, int priority) {
        super(head, body);
        this.priority = priority;
    }

    @Override
    String getSymbol() {
        return " -< ";
    }

    /**
     * returns the translation of this rule as a strict rule
     *
     * @return the translation of this rule as a strict rule
     */
    public StrictRule toStrictRule() {
        return new StrictRule(this.head, this.body);
    }

    /**
     * Get the priority of the rule
     *
     * @return priority of the rule
     */
    public int getPriority() {
        return priority;
    }

    /**
     * Set the priority of the rule
     *
     * @param priority priority of the rule
     */
    public void setPriority(int priority) {
        this.priority = priority;
    }

    @Override
    public RelationalFormula substitute(Term<?> v, Term<?> t) throws IllegalArgumentException {
        return new DefeasibleRule(
                getConclusion().substitute(v, t),
                body.stream()
                        .map(f -> f.substitute(v, t))
                        .collect(Collectors.toSet()), priority);
    }

    @Override
    public RelationalFormula clone() {
        throw new UnsupportedOperationException("IMPLEMENT ME");
    }
}