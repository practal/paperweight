import { beginTheory, declare, axiom, endTheory, includeTheory, have, thm, S, subst, Thm, conclOf, infer } from "../workbench.js";
import "./Minimal-Logic.theory.js";
import { modusPonens, conditionalModusPonens, impliesTrans } from "./Implication.theory.js";

// Modal Logic S4
//
// Normal modal logic with reflexivity and transitivity.
// Kripke frames: preorders (reflexive, transitive relations).
//
// box A = "A is necessarily true" (true in all accessible worlds)

beginTheory();
includeTheory("Minimal-Logic");

declare("box A");

// K axiom: box distributes over implication (normality)
axiom("K", "implies (box (implies A B)) (implies (box A) (box B))");

// T axiom: what is necessary is true (reflexivity)
axiom("T", "implies (box A) A");

// 4 axiom: necessary truths are necessarily necessary (transitivity)
axiom("4", "implies (box A) (box (box A))");

// Necessitation: provable propositions are necessary
axiom("necessitation", "box A", ["A"]);

// Theorems

have("box-implies-refl", "box (implies A A)", [], proveBoxImpliesRefl());
have("box-and", "implies (and (box A) (box B)) (box (and A B))", [], proveBoxAnd());
have("box-and-rev", "implies (box (and A B)) (and (box A) (box B))", [], proveBoxAndRev());

endTheory("S4");

// Helper: apply necessitation rule to a theorem
export function necessitate(t: Thm): Thm {
    const nec = subst(S("A", conclOf(t)), thm("necessitation"));
    return infer(nec, t);
}

function proveBoxImpliesRefl(): Thm {
    // necessitate(implies_refl) = box (implies A A)
    return necessitate(thm("implies_refl"));
}

function proveBoxAnd(): Thm {
    // Goal: implies (and (box A) (box B)) (box (and A B))

    // box (implies A (implies B (and A B)))
    const boxIntro = necessitate(thm("and-intro"));

    // K[B → implies B (and A B)]:
    //   implies (box (implies A (implies B (and A B)))) (implies (box A) (box (implies B (and A B))))
    const k1 = subst(S("B", "implies B (and A B)"), thm("K"));

    // implies (box A) (box (implies B (and A B)))
    const step1 = modusPonens(k1, boxIntro);

    // K[A → B, B → and A B]:
    //   implies (box (implies B (and A B))) (implies (box B) (box (and A B)))
    const k2 = subst(S("A", "B", "B", "and A B"), thm("K"));

    // implies (box A) (implies (box B) (box (and A B)))
    const step2 = impliesTrans(step1, k2);

    // implies (and (box A) (box B)) (box A)
    const elim1 = subst(S("A", "box A", "B", "box B"), thm("and-elim_1"));

    // implies (and (box A) (box B)) (implies (box B) (box (and A B)))
    const step3 = impliesTrans(elim1, step2);

    // implies (and (box A) (box B)) (box B)
    const elim2 = subst(S("A", "box A", "B", "box B"), thm("and-elim_2"));

    // implies (and (box A) (box B)) (box (and A B))
    return conditionalModusPonens(step3, elim2);
}

function proveBoxAndRev(): Thm {
    // Goal: implies (box (and A B)) (and (box A) (box B))

    // K[A → and A B, B → A]:
    //   implies (box (implies (and A B) A)) (implies (box (and A B)) (box A))
    const k1 = subst(S("A", "and A B", "B", "A"), thm("K"));
    // implies (box (and A B)) (box A)
    const boxElim1 = modusPonens(k1, necessitate(thm("and-elim_1")));

    // K[A → and A B]:
    //   implies (box (implies (and A B) B)) (implies (box (and A B)) (box B))
    const k2 = subst(S("A", "and A B"), thm("K"));
    // implies (box (and A B)) (box B)
    const boxElim2 = modusPonens(k2, necessitate(thm("and-elim_2")));

    // implies (box A) (implies (box B) (and (box A) (box B)))
    const intro = subst(S("A", "box A", "B", "box B"), thm("and-intro"));

    // implies (box (and A B)) (implies (box B) (and (box A) (box B)))
    const step1 = impliesTrans(boxElim1, intro);

    // implies (box (and A B)) (and (box A) (box B))
    return conditionalModusPonens(step1, boxElim2);
}
