import { beginTheory, declare, axiom, define, endTheory, lemma, Thm, thm, S, subst,
    includeTheory, 
    have,
    useTheory} from "../workbench.js";
import "./Equality.theory.js";
import { substEquals } from "./Equality.theory.js";
import "./Implication.theory.js";
import { impliesTrans } from "./Implication.theory.js";
import "./Negation.theory.js";

beginTheory();
includeTheory("Implication");
includeTheory("Equality");
declare("for-all (x. A[x])");
axiom("for-all_intro", "for-all (x. A[x])", ["x. A[x]"]);
axiom("for-all_elim", "implies (for-all (x. A[x])) A[x]");
axiom("for-all_distr", "implies (for-all (x. implies A B[x])) (implies A (for-all (x. B[x])))");
define("false", "for-all (x. x)");
have("ex-falso-quodlibet", "implies false P", [], proveExFalsoQuodLibet());
useTheory("Negation");
endTheory("Universal");

beginTheory();
includeTheory("Universal");
axiom("for-all_ext", "equals (for-all (x. A[x])) (for-all (x. B[x]))", ["x. equals A[x] B[x]"]);
endTheory("Universal_Ext");

function proveExFalsoQuodLibet() : Thm {
    // implies false (for-all (x. x))  — via definition of false
    const step1 = subst(S("A", "x. x"), substEquals(thm("false_def")));
    // implies (for-all (x. x)) P  — via for-all elimination
    const step2 = subst(S("A", "x. x", "x", "P"), thm("for-all_elim"));
    // implies false P  — by transitivity
    return impliesTrans(step1, step2);
}