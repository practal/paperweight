import { beginTheory, declare, axiom, endTheory, includeTheory, have, thm, S, subst, Thm, assume, bind } from "../workbench.js";
import "./Implication.theory.js";
import "./Equality.theory.js";
import { modusPonens } from "./Implication.theory.js";
import { substEquals, equalsSym, equalsTrans, congr } from "./Equality.theory.js";

// Quantum Logic — Orthomodular Lattice
//
// A logic whose models include the non-distributive lattices arising in
// quantum mechanics (closed subspaces of a Hilbert space).
//
// DESIGN RATIONALE
// ================
//
// The paperweight framework interprets terms in complete lattices.  An axiom
// with no premises asserts that a term is always the TOP element; a rule
//   P₁, …, Pₙ / C
// asserts  meet(P₁,…,Pₙ) ≤ C  in every model.
//
// Normally, including the Implication theory (K, S, modus-ponens) forces
// models to be Heyting algebras, which are distributive.  However, the
// "Gödel implication" on a complete lattice —
//
//     a → b  =  top   if a ≤ b
//     a → b  =  b     otherwise
//
// satisfies K, S, and modus-ponens on ANY complete lattice, including
// non-distributive ones:
//
//   K  (a → (b → a) = top):
//     If b ≤ a then b → a = top, and a ≤ top.  ✓
//     If b ≰ a then b → a = a, and a ≤ a.  ✓
//
//   S  ((a → (b → c)) → ((a → b) → (a → c)) = top):
//     Verified by exhaustive case analysis on the ordering relations
//     among a, b, c.  The key insight is that whenever the outer
//     antecedent is not top, it equals some lattice element z, and
//     the consequent is always ≥ z.  ✓
//
//   Modus ponens  (meet(a → b, a) ≤ b):
//     If a ≤ b: meet(top, a) = a ≤ b.  ✓
//     If a ≰ b: meet(b, a) ≤ b.  ✓  (meet is always ≤ each argument)
//
// THE QUANTUM SIGNATURE: NO INTERNALIZED MEET-INTRO
// =================================================
//
// The crucial observation is that the Hilbert-style theorem
//
//     implies A (implies B (meet A B))
//
// FAILS on non-distributive lattices with the Gödel implication!
//
// On the diamond lattice M3 = {0, a, b, c, 1} with a, b, c pairwise
// incomparable:
//
//     implies a (implies b (meet a b))
//   = implies a (implies b 0)       -- since meet(a,b) = 0
//   = implies a 0                   -- since b ≰ 0
//   = 0                             -- since a ≰ 0
//   ≠ top  ✗
//
// The failure is specifically about the internalized theorem above.
// It does NOT say that the separate rule
//
//     A, B / meet A B
//
// fails.  In abstraction logic, theoremhood and rule validity are not the
// same thing, and this rule still holds because meet(A, B) <= meet(A, B).
//
// What DOES work on any complete lattice:
//   - meet-elim₁/₂:  implies (meet A B) A           ✓  (meet ≤ each component)
//   - join-intro₁/₂:  implies A (join A B)           ✓  (each component ≤ join)
//   - join-elim:  (A→C) → (B→C) → (A∨B→C)          ✓  (verified case-by-case)
//
// So this theory includes Implication and Equality for reasoning
// infrastructure, declares its own meet/join/ortho without the theorem
//     implies A (implies B (meet A B)),
// and adds the orthomodular law as the characteristic quantum axiom.
//
// PROPER OPERATOR: BIGMEET
// ========================
//
// The infinitary meet  bigmeet (x. A[x])  is a proper operator that binds
// the variable x.  It represents the greatest lower bound of the family
// {A[x] : all x}.  Its intro/elim rules are valid in any complete lattice:
//
//   bigmeet-intro:  from  x. A[x]  (A[x] for arbitrary x), derive bigmeet
//   bigmeet-elim:   implies (bigmeet (x. A[x])) A[x]  (inf ≤ each element)
//
// Unlike for-all in intuitionistic logic, bigmeet does NOT interact well
// with meet (conjunction) — the distributive law
//
//     meet A (bigmeet (x. B[x]))  =  bigmeet (x. meet A B[x])
//
// fails in non-distributive lattices.  This is another quantum feature:
// infinite conjunctions do not distribute over finite ones.

beginTheory();
includeTheory("Implication");
includeTheory("Equality");

// Lattice operations
declare("meet A B");
declare("join A B");

// Orthocomplement (quantum negation)
declare("ortho A");

// Infinitary meet — proper operator binding a variable
declare("bigmeet (x. A[x])");

// ---------------------------------------------------------------------------
// Lattice axioms (valid in any lattice, not just distributive ones)
// ---------------------------------------------------------------------------

// Meet elimination (meet ≤ each component)
axiom("meet-elim_1", "implies (meet A B) A");
axiom("meet-elim_2", "implies (meet A B) B");

// Join introduction (each component ≤ join)
axiom("join-intro_1", "implies A (join A B)");
axiom("join-intro_2", "implies B (join A B)");

// Join elimination (join is least upper bound)
axiom("join-elim", "implies (implies A C) (implies (implies B C) (implies (join A B) C))");

// NOTE: and-intro is deliberately ABSENT — it fails on non-distributive lattices!

// Equational lattice axioms
axiom("meet-comm", "equals (meet A B) (meet B A)");
axiom("join-comm", "equals (join A B) (join B A)");
axiom("meet-assoc", "equals (meet (meet A B) C) (meet A (meet B C))");
axiom("join-assoc", "equals (join (join A B) C) (join A (join B C))");
axiom("meet-idem", "equals (meet A A) A");
axiom("join-idem", "equals (join A A) A");
axiom("absorption-1", "equals (meet A (join A B)) A");
axiom("absorption-2", "equals (join A (meet A B)) A");

// ---------------------------------------------------------------------------
// Orthocomplement axioms (orthocomplemented lattice)
// ---------------------------------------------------------------------------

// Involution: double orthocomplement is identity
axiom("ortho-involution", "equals (ortho (ortho A)) A");

// De Morgan laws (connecting ortho with meet/join)
axiom("de-morgan-meet", "equals (ortho (meet A B)) (join (ortho A) (ortho B))");
axiom("de-morgan-join", "equals (ortho (join A B)) (meet (ortho A) (ortho B))");

// Excluded middle: A ∨ ¬A is always top
// (This is a no-premise axiom, meaning join A (ortho A) = top in every model)
axiom("excluded-middle", "join A (ortho A)");

// ---------------------------------------------------------------------------
// The orthomodular law — the characteristic quantum axiom
// ---------------------------------------------------------------------------
//
// In a Boolean (distributive) algebra, we have full distributivity:
//     A ∨ (B ∧ C) = (A ∨ B) ∧ (A ∨ C)
//
// The orthomodular law is a WEAKER replacement that holds in quantum logic:
//     A ∨ (¬A ∧ (A ∨ B)) = A ∨ B
//
// It says: the "quantum remainder" ¬A ∧ (A ∨ B) — the part of (A ∨ B) that
// is orthogonal to A — when joined back with A, recovers exactly A ∨ B.
//
// This is equivalent to: if A ≤ B then B = A ∨ (¬A ∧ B), i.e., every
// element above A decomposes as A plus its orthogonal complement relative to A.
//
// In quantum mechanics, this corresponds to the fact that any subspace of a
// Hilbert space decomposes as a direct sum of a subspace and its orthogonal
// complement within a larger subspace.

axiom("orthomodular", "equals (join A (meet (ortho A) (join A B))) (join A B)");

// ---------------------------------------------------------------------------
// Infinitary meet — proper operator (binds a variable)
// ---------------------------------------------------------------------------

// Introduction: if A[x] holds for arbitrary x, then bigmeet holds
axiom("bigmeet-intro", "bigmeet (x. A[x])", ["x. A[x]"]);

// Elimination: bigmeet implies each instance
axiom("bigmeet-elim", "implies (bigmeet (x. A[x])) A[x]");

// ---------------------------------------------------------------------------
// Theorems
// ---------------------------------------------------------------------------

// Non-contradiction: meet A (ortho A) is always bottom (its ortho is top).
// Proof: by De Morgan, ortho(meet A (ortho A)) = join (ortho A) (ortho (ortho A))
//      = join (ortho A) A = join A (ortho A) = top (by excluded-middle).
have("non-contradiction", "ortho (meet A (ortho A))", [], proveNonContradiction());

// Join commutativity via implies (from join-intro + join-elim, same pattern as or-comm):
have("join-comm-implies", "implies (join A B) (join B A)", [], proveJoinCommImplies());

// ---------------------------------------------------------------------------
// Notes on unprovable properties
// ---------------------------------------------------------------------------
//
// ORTHO ANTITONICITY (ortho reverses order) is NOT expressible as a rule:
//
//   implies A B / implies (ortho B) (ortho A)     ✗ INVALID
//
// With Gödel implication, the rule requires val(implies A B) ≤ val(implies (ortho B) (ortho A)).
// When A ≰ B (so val(implies A B) = B) and ortho B ≰ ortho A (so val = ortho A),
// this requires B ≤ ortho A, which fails for non-orthogonal elements.
// Counterexample: in the C² subspace lattice, take two non-orthogonal 1D subspaces
// a, b — then a ≰ b and b ≰ ortho(a).
//
// Antitonicity IS valid at the meta-level: if ⊢ implies A B (no premises), then
// ⊢ implies (ortho B) (ortho A). But this is an admissible rule, not derivable
// as a single rule in the object logic.
//
// ORTHO-BIGMEET-ELIM also fails: the direction should be reversed.
// From bigmeet-elim (bigmeet ≤ A[x]), antitonicity gives ortho(A[x]) ≤ ortho(bigmeet),
// i.e., implies (ortho A[x]) (ortho (bigmeet (x. A[x]))) — the opposite direction.
// And even this reversed version requires antitonicity, which is only admissible.

endTheory("Quantum");

function proveNonContradiction(): Thm {
    // Goal: ortho (meet A (ortho A))  [no premises]
    //
    // de-morgan-meet[B→ortho A]: equals (ortho (meet A (ortho A))) (join (ortho A) (ortho (ortho A)))
    const dm = subst(S("B", "ortho A"), thm("de-morgan-meet"));

    // congr ortho-involution into join: equals (join (ortho A) (ortho (ortho A))) (join (ortho A) A)
    const step1 = congr(thm("ortho-involution"), "t. join (ortho A) t");

    // chain: equals (ortho (meet A (ortho A))) (join (ortho A) A)
    const step2 = equalsTrans(dm, step1);

    // join-comm[A→ortho A, B→A]: equals (join (ortho A) A) (join A (ortho A))
    const jc = subst(S("A", "ortho A", "B", "A"), thm("join-comm"));

    // chain: equals (ortho (meet A (ortho A))) (join A (ortho A))
    const step3 = equalsTrans(step2, jc);

    // reverse: equals (join A (ortho A)) (ortho (meet A (ortho A)))
    const step4 = equalsSym(step3);

    // substEquals with identity template: implies (join A (ortho A)) (ortho (meet A (ortho A)))
    const step5 = subst(S("A", "t. t"), substEquals(step4));

    // modusPonens with excluded-middle: ortho (meet A (ortho A))
    return modusPonens(step5, thm("excluded-middle"));
}

function proveJoinCommImplies(): Thm {
    // Goal: implies (join A B) (join B A)  [no premises]
    // Same pattern as or-comm in Minimal-Logic.

    // join-intro_2[B→A, A→B]: implies A (join B A)
    const intro2 = subst(S("B", "A", "A", "B"), thm("join-intro_2"));

    // join-intro_1[A→B, B→A]: implies B (join B A)
    const intro1 = subst(S("A", "B", "B", "A"), thm("join-intro_1"));

    // join-elim[C→join B A]:
    //   implies (implies A (join B A)) (implies (implies B (join B A)) (implies (join A B) (join B A)))
    const elim = subst(S("C", "join B A"), thm("join-elim"));

    const step1 = modusPonens(elim, intro2);
    return modusPonens(step1, intro1);
}
