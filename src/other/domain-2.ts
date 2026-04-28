/*
⏺ Good question. The answer is no — even with just two truth values, minimal implicative logic does not force       
  implication introduction. Here's a concrete counterexample.                                                       
                                                                                                                    
  Counterexample                                                                                                    
                                                                                                                    
  Take U = {0, a, 1} with T = {0, 1}, where |0| = false, |a| = false, |1| = true, and define implies by:            
                                                                                                                    
  ┌─────────┬─────┬─────┬─────┐                                                                                   
  │ implies │  0  │  a  │  1  │
  ├─────────┼─────┼─────┼─────┤
  │ 0       │ 1   │ a   │ 1   │
  ├─────────┼─────┼─────┼─────┤
  │ a       │ 1   │ 1   │ 1   │
  ├─────────┼─────┼─────┼─────┤
  │ 1       │ 0   │ a   │ 1   │
  └─────────┴─────┴─────┴─────┘

  I've verified all 27 instances of implies_2, and the three axioms of minimal implicative logic (modus ponens,
  implies_1, implies_2) all hold in this model.

  But ImpliesIntro fails: |0| = false and |a| = false, so |0| ≤ |a| holds trivially, yet |implies(0, a)| = |a| =
  false.

  Why it happens

  The element a is "junk" — it has truth value false, just like 0, but implies doesn't treat it the same as 0. The
  operation implies is only constrained by the axioms at the level of truth values for certain patterns (e.g.,
  implies_1 forces |implies(u, v)| = true when |v| = true), but it leaves room for |implies(u, v)| = false when both
   |u| and |v| are false, provided the offending output is a different false-valued element than the one the axioms
  check.

  Concretely, implies_1 forces |implies(0, implies(v, 0))| = true for all v, but implies(v, 0) is always either 0 or
   1 in this model — never a. So the axioms never directly constrain |implies(0, a)|.

  What this means

  Even the two-valued Boolean case doesn't collapse the distinction between minimal implicative logic and
  ImpliesIntro. To get ImpliesIntro, you genuinely need to impose that the logical order is a Heyting algebra and
  that implies is the Heyting implication — the axioms of minimal implicative logic alone aren't enough, regardless
  of the size of T.

  This suggests that completeness for the extended system (Pure Deduction + ImpliesIntro) would require restricting
  to Heyting models, and the Rasiowa construction would need adaptation — it's not obvious the de Bruijn algebra
  naturally carries a Heyting structure.
  
*/
  
export const DOMAIN = [0, 1, 2];

export type Domain = number;

export function checkDomain(a : Domain) {
    if (a === 0 || a === 1 || a === 2) return;
    throw new Error("Value is not in domain: " + a);
}

export function isTrue(a : Domain) : boolean {
    checkDomain(a);
    return a === 2;
}

export function meet(a : Domain, b : Domain) : Domain {
    checkDomain(a);
    checkDomain(b);
    if (a === 2 && b === 2) return 2; else return 0;
}

export function leq(a : Domain, b : Domain) : boolean {
    checkDomain(a);
    checkDomain(b);
    if (b === 2) return true;
    if (a === 2) return false;
    return true;
}
