import { beginTheory, declare, axiom, endTheory, includeTheory, have, thm, S, subst, Thm, infer } from "../workbench.js";
import "./Implication.theory.js";

// Kripke-style S4 Modal Logic with Proper Operators
//
// Unlike S4.theory.ts where box takes a term (arity 0),
// here nec takes an explicit world parameter and binds a world variable:
//
//   nec w (v. A[v])  =  "A holds at all worlds accessible from w"
//
// This makes the world quantification explicit via a proper operator (arity 1).

beginTheory();
includeTheory("Implication");

declare("nec w (v. A[v])");

// Necessitation: universal truths are necessary
axiom("nec-intro", "nec w (v. A[v])", ["v. A[v]"]);

// K: distribution of necessity over implication
axiom("nec-K", "implies (nec w (v. implies A[v] B[v])) (implies (nec w (v. A[v])) (nec w (v. B[v])))");

// T: reflexivity — the source world is accessible from itself
axiom("nec-T", "implies (nec w (v. A[v])) A[w]");

// 4: transitivity — positive introspection
axiom("nec-4", "implies (nec w (v. A[v])) (nec w (v. nec v (u. A[u])))");

// Theorem: tautologies are necessary
have("nec-refl", "nec w (v. implies v v)", [], proveNecRefl());

// Theorem: iterated necessity collapses — nec nec A implies nec A
have("nec-collapse", "implies (nec w (v. nec v (u. A[u]))) (nec w (u. A[u]))", [],
    proveNecCollapse());

endTheory("Kripke-S4");

function proveNecRefl(): Thm {
    // nec-intro with A → (v. implies v v):
    //   premise: v. implies v v   conclusion: nec w (v. implies v v)
    // implies_refl[A→v]: implies v v (with v free)
    // infer matches free v against binder v in the template premise
    const nec = subst(S("A", "v. implies v v"), thm("nec-intro"));
    const refl = subst(S("A", "v"), thm("implies_refl"));
    return infer(nec, refl);
}

function proveNecCollapse(): Thm {
    // nec-T: implies (nec w (v. A[v])) A[w]
    // Substitute A (arity 1) → (v. nec v (u. A[u])):
    //   A[v] → nec v (u. A[u])
    //   A[w] → nec w (u. A[u])
    // Result: implies (nec w (v. nec v (u. A[u]))) (nec w (u. A[u]))
    return subst(S("A", "v. nec v (u. A[u])"), thm("nec-T"));
}
