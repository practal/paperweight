import { beginTheory, declare, axiom, endTheory, includeTheory, have, thm, S, subst, Thm } from "../workbench.js";
import "./Positive-Logic.theory.js";
import "./Equality.theory.js";
import { modusPonens, impliesTrans, conditionalModusPonens } from "./Implication.theory.js";

// LP-style Paraconsistent De Morgan Logic
//
// Intended Semantics: 3-element lattice {0 < 1 < 2} with Heyting implication,
// LP negation (involution: not(0)=2, not(1)=1, not(2)=0), and=min, or=max.
//
// Key properties:
// - No explosion (and A (not A) does NOT imply B)
// - Double negation holds in both directions
// - All four De Morgan laws hold
// - Excluded middle does NOT hold

beginTheory();
includeTheory("Positive-Logic");

declare("not A");

// Double negation
axiom("double-neg-intro", "implies A (not (not A))");
axiom("double-neg-elim", "implies (not (not A)) A");

// De Morgan laws
axiom("de-morgan_1", "implies (not (and A B)) (or (not A) (not B))");
axiom("de-morgan_2", "implies (or (not A) (not B)) (not (and A B))");
axiom("de-morgan_3", "implies (not (or A B)) (and (not A) (not B))");
axiom("de-morgan_4", "implies (and (not A) (not B)) (not (or A B))");

// Non-contradiction implies excluded middle
have("non-contradiction-implies-em", "implies (not (and A (not A))) (or A (not A))", [],
    proveNonContradictionImpliesEM());

endTheory("Paraconsistent-Logic");

function proveNonContradictionImpliesEM() : Thm {
    // Goal: implies (not (and A (not A))) (or A (not A))

    // Step 1: de-morgan_1[B→not A]: implies (not (and A (not A))) (or (not A) (not (not A)))
    const dm1 = subst(S("B", "not A"), thm("de-morgan_1"));

    // Step 2: implies (not A) (or (not A) A)
    // or-intro_1[A→not A, B→A]: implies (not A) (or (not A) A)
    const branch1 = subst(S("A", "not A", "B", "A"), thm("or-intro_1"));

    // Step 3: implies (not (not A)) (or (not A) A)
    // double-neg-elim: implies (not (not A)) A
    // or-intro_2[A→not A, B→A]: implies A (or (not A) A)
    // chain: implies (not (not A)) (or (not A) A)
    const dne = thm("double-neg-elim");
    const intro2 = subst(S("A", "not A", "B", "A"), thm("or-intro_2"));
    const branch2 = impliesTrans(dne, intro2);

    // Step 4: or-elim[A→not A, B→not (not A), C→or (not A) A]:
    //   implies (or (not A) (not (not A))) (or (not A) A)
    const elim = subst(S("A", "not A", "B", "not (not A)", "C", "or (not A) A"), thm("or-elim"));
    const step4 = modusPonens(modusPonens(elim, branch1), branch2);

    // Step 5: chain with dm1: implies (not (and A (not A))) (or (not A) A)
    const step5 = impliesTrans(dm1, step4);

    // Step 6: compose with or-comm: implies (not (and A (not A))) (or A (not A))
    const comm = subst(S("A", "not A", "B", "A"), thm("or-comm"));
    return impliesTrans(step5, comm);
}
