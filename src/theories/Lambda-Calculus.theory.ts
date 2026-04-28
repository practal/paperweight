import { beginTheory, declare, axiom, define, endTheory, includeTheory, have, thm, S, subst, Thm, sorry } from "../workbench.js";
import "./Pure-Equality.theory.js";
import { congr, equalsSym, equalsTrans } from "./Pure-Equality.theory.js";

beginTheory();
includeTheory("Pure-Equality"); // Instead of Equality, which already includes Implication.

// Core untyped lambda calculus primitives:
// lambda abstraction is a proper operator, application is an ordinary operation.
declare("lam (x. M[x])");
declare("app F X");

// Beta and eta describe the computational behavior of lambda terms.
axiom("beta",
    "equals (app (lam (x. M[x])) N) M[N]");
axiom("eta",
    "equals (lam (x. app F x)) F");

// Standard combinators and self-application gadgets.
define("I", "lam (x. x)");
define("K", "lam (x. lam (y. x))");
define("S", "lam (f. lam (g. lam (x. app (app f x) (app g x))))");
define("compose F G", "lam (x. app F (app G x))");
define("delta", "lam (x. app x x)");
define("Omega", "app delta delta");
define("Y", "lam (f. app (lam (x. app f (app x x))) (lam (x. app f (app x x))))");
have("I-beta",
    "equals (app I M) M", [],
    proveIBeta());
have("K-beta",
    "equals (app (app K M) N) M", [],
    proveKBeta());
have("S-beta",
    "equals (app (app (app S F) G) X) (app (app F X) (app G X))", [],
    proveSBeta());
have("compose-beta",
    "equals (app (compose F G) X) (app F (app G X))", [],
    proveComposeBeta());
have("SKK-is-I-on-X",
    "equals (app (app (app S K) K) X) X", [],
    proveSKKIsIOnX());
have("delta-omega",
    "equals (app delta delta) Omega", [],
    proveDeltaOmega());
have("Y-unroll",
    "equals (app Y F) (app F (app Y F))", [],
    proveYUnroll());

endTheory("Lambda-Calculus");

function instantiate(label: string, ...varsAndTerms: string[]): Thm {
    return varsAndTerms.length === 0 ? thm(label) : subst(S(...varsAndTerms), thm(label));
}

function betaReduce(bodyTemplate: string, arg: string): Thm {
    return instantiate("beta", "M", bodyTemplate, "N", arg);
}

function etaReduce(fn: string): Thm {
    return instantiate("eta", "F", fn);
}

function applyDefinition(defLabel: string, outerTemplate: string, ...varsAndTerms: string[]): Thm {
    return congr(instantiate(defLabel, ...varsAndTerms), outerTemplate);
}

function chainEquals(...steps: Thm[]): Thm {
    if (steps.length === 0) throw new Error("chainEquals: expected at least one step.");
    return steps.slice(1).reduce((acc, step) => equalsTrans(acc, step), steps[0]);
}

// Informal proof sketch.
// Unfold I to the identity abstraction and beta-reduce once.
//
// Formal proof sketch.
// 1. equals (app I M) (app (lam (x. x)) M)               [I_def by congruence]
// 2. equals (app (lam (x. x)) M) M                       [beta]
// 3. equals (app I M) M                                  [transitivity]
function proveIBeta(): Thm {
    if (false) {
        const step1 = sorry("equals (app I M) (app (lam (x. x)) M)");
        const step2 = sorry("equals (app (lam (x. x)) M) M");
        const _final = equalsTrans(step1, step2);
        void _final;
    }

    return chainEquals(
        applyDefinition("I_def", "t. app t M"),
        betaReduce("x. x", "M"),
    );
}

// Informal proof sketch.
// Unfold K, beta-reduce the outer abstraction to a constant function,
// then beta-reduce that constant function on the second argument.
//
// Formal proof sketch.
// 1. equals (app (app K M) N) (app (app (lam (x. lam (y. x))) M) N)
// 2. equals (app (app (lam (x. lam (y. x))) M) N) (app (lam (y. M)) N)
// 3. equals (app (lam (y. M)) N) M
// 4. equals (app (app K M) N) M
function proveKBeta(): Thm {
    if (false) {
        const step1 = sorry("equals (app (app K M) N) (app (app (lam (x. lam (y. x))) M) N)");
        const step2 = sorry("equals (app (app (lam (x. lam (y. x))) M) N) (app (lam (y. M)) N)");
        const step3 = sorry("equals (app (lam (y. M)) N) M");
        const _final = chainEquals(step1, step2, step3);
        void _final;
    }

    return chainEquals(
        applyDefinition("K_def", "t. app (app t M) N"),
        congr(betaReduce("x. lam (y. x)", "M"), "t. app t N"),
        betaReduce("y. M", "N"),
    );
}

// Informal proof sketch.
// Unfold S and beta-reduce three times, once for each lambda binder.
//
// Formal proof sketch.
// 1. equals (app (app (app S F) G) X) (app (app (app (lam ...) F) G) X)
// 2. equals (app (app (app (lam ...) F) G) X) (app (app (lam ...) G) X)
// 3. equals (app (app (lam ...) G) X) (app (lam (x. app (app F x) (app G x))) X)
// 4. equals (app (lam (x. app (app F x) (app G x))) X) (app (app F X) (app G X))
function proveSBeta(): Thm {
    if (false) {
        const step1 = sorry("equals (app (app (app S F) G) X) (app (app (app (lam (f. lam (g. lam (x. app (app f x) (app g x))))) F) G) X)");
        const step2 = sorry("equals (app (app (app (lam (f. lam (g. lam (x. app (app f x) (app g x))))) F) G) X) (app (app (lam (g. lam (x. app (app F x) (app g x)))) G) X)");
        const step3 = sorry("equals (app (app (lam (g. lam (x. app (app F x) (app g x)))) G) X) (app (lam (x. app (app F x) (app G x))) X)");
        const step4 = sorry("equals (app (lam (x. app (app F x) (app G x))) X) (app (app F X) (app G X))");
        const _final = chainEquals(step1, step2, step3, step4);
        void _final;
    }

    return chainEquals(
        applyDefinition("S_def", "t. app (app (app t F) G) X"),
        congr(betaReduce("f. lam (g. lam (x. app (app f x) (app g x)))", "F"), "t. app (app t G) X"),
        congr(betaReduce("g. lam (x. app (app F x) (app g x))", "G"), "t. app t X"),
        betaReduce("x. app (app F x) (app G x)", "X"),
    );
}

// Informal proof sketch.
// Unfold composition and beta-reduce the resulting lambda.
//
// Formal proof sketch.
// 1. equals (app (compose F G) X) (app (lam (x. app F (app G x))) X)
// 2. equals (app (lam (x. app F (app G x))) X) (app F (app G X))
// 3. equals (app (compose F G) X) (app F (app G X))
function proveComposeBeta(): Thm {
    if (false) {
        const step1 = sorry("equals (app (compose F G) X) (app (lam (x. app F (app G x))) X)");
        const step2 = sorry("equals (app (lam (x. app F (app G x))) X) (app F (app G X))");
        const _final = equalsTrans(step1, step2);
        void _final;
    }

    return chainEquals(
        applyDefinition("compose_def", "t. app t X"),
        betaReduce("x. app F (app G x)", "X"),
    );
}

// Informal proof sketch.
// Reduce S K K at X using S-beta, then reduce the resulting K-redex.
//
// Formal proof sketch.
// 1. equals (app (app (app S K) K) X) (app (app K X) (app K X))
// 2. equals (app (app K X) (app K X)) X
// 3. equals (app (app (app S K) K) X) X
function proveSKKIsIOnX(): Thm {
    if (false) {
        const step1 = sorry("equals (app (app (app S K) K) X) (app (app K X) (app K X))");
        const step2 = sorry("equals (app (app K X) (app K X)) X");
        const _final = equalsTrans(step1, step2);
        void _final;
    }

    return chainEquals(
        instantiate("S-beta", "F", "K", "G", "K", "X", "X"),
        instantiate("K-beta", "M", "X", "N", "app K X"),
    );
}

// Informal proof sketch.
// Omega is defined to be delta applied to itself, so the theorem is just the
// symmetric form of the definition.
//
// Formal proof sketch.
// 1. equals Omega (app delta delta)                      [Omega_def]
// 2. equals (app delta delta) Omega                     [symmetry]
function proveDeltaOmega(): Thm {
    if (false) {
        const step1 = sorry("equals Omega (app delta delta)");
        const _final = sorry("equals (app delta delta) Omega");
        void step1;
        void _final;
    }

    return equalsSym(thm("Omega_def"));
}

// Informal proof sketch.
// Unfold Y and beta-reduce once to get the standard self-application body.
// Beta-reduce that body once more:
//   app (lam (x. app F (app x x))) (lam (x. app F (app x x)))
//   = app F (app (lam (x. app F (app x x))) (lam (x. app F (app x x)))).
// Finally rewrite the recursive occurrence back to app Y F under app F.
//
// Formal proof sketch.
// 1. equals (app Y F) BODY
// 2. equals BODY (app F BODY)
// 3. equals (app F BODY) (app F (app Y F))
// 4. equals (app Y F) (app F (app Y F))
function proveYUnroll(): Thm {
    if (false) {
        const step1 = sorry("equals (app Y F) (app (lam (x. app F (app x x))) (lam (x. app F (app x x))))");
        const step2 = sorry("equals (app (lam (x. app F (app x x))) (lam (x. app F (app x x)))) (app F (app (lam (x. app F (app x x))) (lam (x. app F (app x x)))))");
        const step3 = sorry("equals (app F (app (lam (x. app F (app x x))) (lam (x. app F (app x x))))) (app F (app Y F))");
        const _final = chainEquals(step1, step2, step3);
        void _final;
    }

    const yToBody = chainEquals(
        applyDefinition("Y_def", "t. app t F"),
        betaReduce("f. app (lam (x. app f (app x x))) (lam (x. app f (app x x)))", "F"),
    );
    const bodyToRecursive = betaReduce("x. app F (app x x)", "lam (x. app F (app x x))");
    const recursiveToY = equalsSym(congr(yToBody, "t. app F t"));
    return chainEquals(yToBody, bodyToRecursive, recursiveToY);
}
