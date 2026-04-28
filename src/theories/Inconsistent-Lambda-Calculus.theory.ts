import { beginTheory, define, endTheory, have, includeTheory, infer, S, sorry, subst, thm, Thm } from "../workbench.js";
import { transportProvenEquality } from "../proof-tools/pure-equality.js";
import "./Implication.theory.js";
import "./Lambda-Calculus.theory.js";
import { modusPonens } from "./Implication.theory.js";
import { congr, equalsSym, equalsTrans } from "./Pure-Equality.theory.js";

beginTheory();
includeTheory("Implication");
includeTheory("Lambda-Calculus");

define("Curry P", "app Y (lam (c. implies c P))");

have("curry-fixed-point",
    "equals (Curry P) (implies (Curry P) P)", [],
    proveCurryFixedPoint());

have("inconsistency",
    "P", [],
    proveInconsistency());

endTheory("Inconsistent-Lambda-Calculus");

function instantiate(label: string, ...varsAndTerms: string[]): Thm {
    return varsAndTerms.length === 0 ? thm(label) : subst(S(...varsAndTerms), thm(label));
}

// Informal proof sketch.
// Unfold Curry P to its definition app Y (lam (c. implies c P)).
// Then use Y-unroll once:
//   app Y F = app F (app Y F)
// with F := lam (c. implies c P).
// A beta-step turns the right-hand side into implies (Curry P) P.
//
// Formal proof sketch.
// 1. equals (Curry P) BODY
// 2. equals BODY (app (lam (c. implies c P)) BODY)
// 3. equals (app (lam (c. implies c P)) BODY) (implies BODY P)
// 4. equals (implies BODY P) (implies (Curry P) P)
// 5. equals (Curry P) (implies (Curry P) P)
function proveCurryFixedPoint(): Thm {
    if (false) {
        const step1 = sorry("equals (Curry P) (app Y (lam (c. implies c P)))");
        const step2 = sorry("equals (app Y (lam (c. implies c P))) (app (lam (c. implies c P)) (app Y (lam (c. implies c P))))");
        const step3 = sorry("equals (app (lam (c. implies c P)) (app Y (lam (c. implies c P)))) (implies (app Y (lam (c. implies c P))) P)");
        const step4 = sorry("equals (implies (app Y (lam (c. implies c P))) P) (implies (Curry P) P)");
        const _final = sorry("equals (Curry P) (implies (Curry P) P)");
        void step1;
        void step2;
        void step3;
        void step4;
        void _final;
    }

    const body = "app Y (lam (c. implies c P))";
    const curryDef = thm("Curry_def");
    const yUnroll = instantiate("Y-unroll", "F", "lam (c. implies c P)");
    const beta = instantiate("beta", "M", "c. implies c P", "N", body);
    const rewriteRhs = equalsSym(congr(curryDef, "t. implies t P"));
    return equalsTrans(curryDef,
        equalsTrans(yUnroll,
            equalsTrans(beta, rewriteRhs)));
}

// Informal proof sketch.
// Let C := Curry P. The fixed-point theorem gives
//   C = (C -> P).
// Equality substitution with the identity template yields both directions:
//   C -> (C -> P)
//   (C -> P) -> C.
// By implicational contraction we derive C -> P from the first direction.
// Then modus ponens with the second direction gives C, and another modus
// ponens yields P.
//
// Formal proof sketch.
// 1. equals (Curry P) (implies (Curry P) P)
// 2. implies (Curry P) (implies (Curry P) P)
// 3. implies (implies (Curry P) P) (Curry P)
// 4. implies (Curry P) P
// 5. Curry P
// 6. P
function proveInconsistency(): Thm {
    if (false) {
        const step1 = sorry("equals (Curry P) (implies (Curry P) P)");
        const step2 = sorry("implies (Curry P) (implies (Curry P) P)");
        const step3 = sorry("implies (implies (Curry P) P) (Curry P)");
        const step4 = sorry("implies (Curry P) P");
        const step5 = sorry("Curry P");
        const _final = sorry("P");
        void step1;
        void step2;
        void step3;
        void step4;
        void step5;
        void _final;
    }

    const fixed = thm("curry-fixed-point");
    const forward = transportProvenEquality(fixed);
    const backward = transportProvenEquality(equalsSym(fixed));
    const contraction = infer(
        instantiate("implies_contraction", "A", "Curry P", "B", "P"),
        forward,
    );
    const curry = modusPonens(backward, contraction);
    return modusPonens(contraction, curry);
}
