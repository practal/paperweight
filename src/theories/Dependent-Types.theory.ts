import { beginTheory, declare, axiom, endTheory, includeTheory, conjecture } from "../workbench.js";
import "./Implication.theory.js";
import "./Equality.theory.js";

beginTheory();
includeTheory("Implication");
includeTheory("Equality");

// === Typing judgment and universe ===
declare("hastype M A");
declare("U");

// === Dependent function type (Pi) ===
declare("Pi A (x. B[x])");
declare("lam A (x. M[x])");
declare("app M N");

// === Dependent pair type (Sigma) ===
declare("Sigma A (x. B[x])");
declare("pair A (x. B[x]) M N");
declare("fst P");
declare("snd P");

// === Identity type ===
declare("Id A M N");
declare("refl M");
declare("J A (x p. C[x, p]) D M N Q");

// ============================================================
// Universe Formation Axioms
// ============================================================

// Pi-type formation: if A : U and B[x] : U for all x : A, then Pi A B : U
axiom("U-Pi",
    "implies (hastype A U) (hastype (Pi A (x. B[x])) U)",
    ["x. implies (hastype x A) (hastype B[x] U)"]);

// Sigma-type formation: if A : U and B[x] : U for all x : A, then Sigma A B : U
axiom("U-Sigma",
    "implies (hastype A U) (hastype (Sigma A (x. B[x])) U)",
    ["x. implies (hastype x A) (hastype B[x] U)"]);

// Id-type formation: if A : U and M, N : A, then Id A M N : U
axiom("U-Id",
    "implies (hastype A U) (implies (hastype M A) (implies (hastype N A) (hastype (Id A M N) U)))");

// ============================================================
// Pi-type Rules
// ============================================================

// Pi-intro: if M[x] : B[x] for all x : A, and A : U, then lam A (x. M[x]) : Pi A (x. B[x])
axiom("Pi-intro",
    "implies (hastype A U) (hastype (lam A (x. M[x])) (Pi A (x. B[x])))",
    ["x. implies (hastype x A) (hastype M[x] B[x])"]);

// Pi-elim: if F : Pi A (x. B[x]) and M : A, then app F M : B[M]
axiom("Pi-elim",
    "implies (hastype F (Pi A (x. B[x]))) (implies (hastype M A) (hastype (app F M) B[M]))");

// Pi-beta: app (lam A (x. M[x])) N = M[N] when N : A
axiom("Pi-beta",
    "implies (hastype N A) (equals (app (lam A (x. M[x])) N) M[N])");

// Pi-eta: if F : Pi A (x. B[x]) then F = lam A (x. app F x)
axiom("Pi-eta",
    "implies (hastype F (Pi A (x. B[x]))) (equals F (lam A (x. app F x)))");

// ============================================================
// Sigma-type Rules
// ============================================================

// Sigma-intro: if M : A and N : B[M], and A : U, then pair : Sigma A (x. B[x])
axiom("Sigma-intro",
    "implies (hastype A U) (implies (hastype M A) (implies (hastype N B[M]) (hastype (pair A (x. B[x]) M N) (Sigma A (x. B[x])))))");

// Sigma-fst: if P : Sigma A (x. B[x]), then fst P : A
axiom("Sigma-fst",
    "implies (hastype P (Sigma A (x. B[x]))) (hastype (fst P) A)");

// Sigma-snd: if P : Sigma A (x. B[x]), then snd P : B[fst P]
axiom("Sigma-snd",
    "implies (hastype P (Sigma A (x. B[x]))) (hastype (snd P) B[fst P])");

// Sigma-beta-fst: fst (pair A B M N) = M
axiom("Sigma-beta-fst",
    "equals (fst (pair A (x. B[x]) M N)) M");

// Sigma-beta-snd: snd (pair A B M N) = N
axiom("Sigma-beta-snd",
    "equals (snd (pair A (x. B[x]) M N)) N");

// ============================================================
// Identity Type Rules
// ============================================================

// Id-intro: if M : A, then refl M : Id A M M
axiom("Id-intro",
    "implies (hastype M A) (hastype (refl M) (Id A M M))");

// Id-elim (J): transport/elimination rule
// If we have a proof Q : Id A M N, a motive C[x,p] for x:A and p:Id A M x,
// a base case D : C[M, refl M], then J ... Q : C[N, Q]
axiom("Id-elim",
    "implies (hastype Q (Id A M N)) (implies (hastype D C[M, refl M]) (hastype (J A (x p. C[x, p]) D M N Q) C[N, Q]))",
    ["x p. implies (hastype x A) (implies (hastype p (Id A M x)) (hastype C[x, p] U))"]);

// Id-beta: J ... (refl M) computes to D
axiom("Id-beta",
    "equals (J A (x p. C[x, p]) D M M (refl M)) D");

// ============================================================
// Conjectures (theorems to prove later)
// ============================================================

// The identity function is well-typed at any type
conjecture("id-welltyped",
    "implies (hastype A U) (hastype (lam A (x. x)) (Pi A (x. A)))",
    []);

// The constant function (K combinator) is well-typed
conjecture("const-welltyped",
    "implies (hastype A U) (implies (hastype B U) (implies (hastype M A) (hastype (lam B (x. M)) (Pi B (x. A)))))",
    []);

// First projection of a pair computes correctly
conjecture("pair-fst-beta",
    "equals (fst (pair A (x. B[x]) M N)) M",
    []);

// If two functions are equal and two arguments are equal, applications are equal
conjecture("app-preserves-eq",
    "implies (equals F G) (implies (equals M N) (equals (app F M) (app G N)))",
    []);

endTheory("Dependent-Types");
