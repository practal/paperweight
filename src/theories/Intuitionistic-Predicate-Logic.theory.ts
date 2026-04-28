import { axiom, beginTheory, declare, define, endTheory, exportTeX, includeTheory } from "../workbench.js";
import "./Minimal-Logic.theory.js";

beginTheory();
includeTheory("Implication");
includeTheory("Equality");
declare("for-all (x. A[x])");
axiom("for-all-intro", "for-all (x. A[x])", ["x. A[x]"]);
axiom("for-all_1", "implies (for-all (x. A[x])) A[x]");
axiom("for-all_2", "implies (for-all (x. implies A B[x])) (implies A (for-all (x. B[x])))");
declare("exists (x. A[x])");
axiom("exists-intro", "implies A[x] (exists (x. A[x]))");
axiom("exists-elim", "C", ["exists (x. A[x])", "x. implies A[x] C"]);
define("false", "for-all (x. x)");
includeTheory("Minimal-Logic");
endTheory("Intuitionistic-Predicate-Logic");

// exportTeX("Intuitionistic-Predicate-Logic");

