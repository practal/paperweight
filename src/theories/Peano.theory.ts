import { beginTheory, declare, axiom, endTheory, define, includeTheory, thm, S, subst, Thm, infer } from "../workbench.js";
import "./Negation.theory.js";
import { conditionalModusPonens, weaken } from "./Implication.theory.js";

beginTheory();
includeTheory("Implication");
includeTheory("Equality");
includeTheory("Negation");
declare("Nat n");
declare("zero");
declare("succ n");
define("one", "succ zero");
axiom("Nat-zero", "Nat zero");
axiom("Nat-succ", "implies (Nat n) (Nat (succ n))");
axiom("Nat-equals-succ", "implies (Nat m) (implies (Nat n) (implies (equals (succ m) (succ n)) (equals m n)))");
axiom("Nat-equals-zero", "implies (Nat n) (not-equals zero (succ n))");
axiom("Nat-induct", "implies (Nat n) (implies A[zero] A[n])", ["n. implies (Nat n) (implies A[n] A[succ n])"]);
endTheory("Peano");

export function inductNat(property : string, step : Thm, base : Thm) : Thm {
    const ind = subst(S("A", property), thm("Nat-induct"));
    const afterStep = infer(ind, step);
    const weakBase = weaken(base, "Nat n");
    return conditionalModusPonens(afterStep, weakBase);
}
