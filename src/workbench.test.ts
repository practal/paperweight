import { assertCrashT, assertEqT, Test } from "things";
import { declare, axiom, endTheory, beginTheory, includeTheory, define, defineAs,
    defineWith, defineWithAs, display, conclOf, thm, subst, S, infer, have } from "./workbench.js";

beginTheory();
declare("implies A B")
axiom("Modus-ponens", "B", ["implies A B", "A"])
axiom("Implication_1", "implies B A", ["A"])
axiom("Implication_2", "implies A C", ["implies A (implies B C)", "implies A B"])
endTheory("WB_Implication");

beginTheory();
declare("equals x y");
axiom("Equality_1", "equals x x");
axiom("Equality_2", "A[y]", ["equals x y", "A[x]"]);
endTheory("WB_Equality");

beginTheory();
includeTheory("WB_Implication");
includeTheory("WB_Equality");
declare("false");
axiom("ex-falso-quodlibet", "P", ["false"]);
define("not A", "implies A false");
define("not-equals x y", "not (equals x y)");
endTheory("WB_Negation");

beginTheory();
includeTheory("WB_Implication");
includeTheory("WB_Equality");
includeTheory("WB_Negation");
declare("Nat n");
declare("zero");
declare("succ n");
axiom("Nat-zero", "Nat zero");
axiom("Nat-succ", "Nat (succ n)");
axiom("Nat-equals-succ", "equals m n", ["Nat m", "Nat n", "equals (succ m) (succ n)"]);
axiom("Nat-equals-zero", "not-equals zero (succ n)", ["Nat n"]);
axiom("Nat-induct", "A[n]", ["Nat n", "A[zero]", "n. implies (Nat n) (implies A[n] A[succ n])"]);
endTheory("WB_PeanoSC");

Test(() => {
    beginTheory();
    includeTheory("WB_PeanoSC");
    defineAs("u1", "u x", "succ x");
    endTheory("u1");

    beginTheory();
    includeTheory("WB_PeanoSC");
    defineAs("u2", "u y", "succ y");
    endTheory("u2");

    beginTheory();
    includeTheory("WB_PeanoSC");
    defineAs("u3", "u x", "succ x");
    endTheory("u3");

    assertCrashT(() => {
        beginTheory();
        includeTheory("u1");
        includeTheory("u2");
        endTheory("u12");
    });

    beginTheory();
    includeTheory("u1");
    includeTheory("u3");
    endTheory("u13");

});

Test(() => {
    beginTheory();
    includeTheory("WB_Equality");
    defineWith("x y. equals x y", "id x", "x");
    assertEqT(display(conclOf(thm("id_def"))), "equals (id x) x");
    endTheory("defineWith-equality");
}, "defineWith equality compatibility");

Test(() => {
    beginTheory();
    includeTheory("WB_Implication");
    includeTheory("WB_Equality");
    declare("unit");
    axiom("unit_true", "unit");
    have("unit_equals_refl", "implies unit (equals x x)", [], infer(
        subst(S("A", "equals x x", "B", "unit"), thm("Implication_1")),
        thm("Equality_1")));
    defineWith("x y. implies unit (equals x y)", "guarded x", "x");
    assertEqT(display(conclOf(thm("guarded_def"))), "implies unit (equals (guarded x) x)");
    endTheory("defineWith-guarded");
}, "defineWith guarded relation");

Test(() => {
    assertCrashT(() => {
        beginTheory();
        includeTheory("WB_Equality");
        defineWith("x y. equals P x", "bad x", "x");
    });

    assertCrashT(() => {
        beginTheory();
        declare("bad x y");
        defineWith("x y. bad x y", "u x", "x");
    });

    assertCrashT(() => {
        beginTheory();
        includeTheory("WB_Equality");
        defineWith("x y. equals x y", "loop x", "loop x");
    });
}, "defineWith validation failures");

Test(() => {
    beginTheory();
    includeTheory("WB_Equality");
    defineWithAs("u_eq", "x y. equals x y", "u x", "x");
    endTheory("u-eq");

    beginTheory();
    includeTheory("WB_Equality");
    defineWithAs("u_rev", "x y. equals y x", "u x", "x");
    endTheory("u-rev");

    assertCrashT(() => {
        beginTheory();
        includeTheory("u-eq");
        includeTheory("u-rev");
        endTheory("u-mixed");
    });
}, "defineWith import clash");
