import { beginTheory, includeTheory, declare, axiom, define, endTheory, have, thm, S, subst, Thm, parse, assume } from "../workbench.js";
import "./Implication.theory.js";
import "./Equality.theory.js";
import { modusPonens, impliesExchange, impliesRefl, conditionalModusPonens, applyInContext, impliesTrans, conditionalImpliesTrans } from "./Implication.theory.js";
import { foldDefinition, transportDefinitionRenamed } from "../proof-tools/definitions.js";
import { forAllIntroFrom } from "../proof-tools/quantifiers.js";
import { app, lam, provePureImplication, tyAtom, tyImp, v } from "../proof-tools/pure-implication.js";

beginTheory();
includeTheory("Implication");
includeTheory("Equality");

declare("for-all (x. A[x])");
axiom("for-all_intro", "for-all (x. A[x])", ["x. A[x]"]);
axiom("for-all_elim", "implies (for-all (x. A[x])) A[x]");
axiom("for-all_distr", "implies (for-all (x. implies A B[x])) (implies A (for-all (x. B[x])))");

define("false", "for-all (x. x)");
define("true", "implies false false");
define("not A", "implies A false");
define("or A B", "implies (not A) B");
define("and A B", "not (implies A (not B))");
define("equiv A B", "and (implies A B) (implies B A)");
define("exists (x. A[x])", "not (for-all (x. not A[x]))");

axiom("double-negation-elim", "implies (not (not A)) A");

// --- Derived theorems ---

have("ex-falso", "implies false P", [], proveExFalso());
have("excluded-middle", "or A (not A)", [], proveExcludedMiddle());
have("or_intro_1", "implies A (or A B)", [], proveOrIntro1());
have("or_intro_2", "implies B (or A B)", [], proveOrIntro2());
have("or_elim", "implies (implies A C) (implies (implies B C) (implies (or A B) C))", [], proveOrElim());
have("and_intro", "implies A (implies B (and A B))", [], proveAndIntro());
have("and_elim_1", "implies (and A B) A", [], proveAndElim1());
have("and_elim_2", "implies (and A B) B", [], proveAndElim2());
have("equiv_intro", "implies (implies A B) (implies (implies B A) (equiv A B))", [], proveEquivIntro());
have("equiv_elim_1", "implies (equiv A B) (implies A B)", [], proveEquivElim1());
have("equiv_elim_2", "implies (equiv A B) (implies B A)", [], proveEquivElim2());
have("exists_intro", "implies A[x] (exists (x. A[x]))", [], proveExistsIntro());
have("exists_elim", "C", ["exists (x. A[x])", "x. implies A[x] C"], proveExistsElim());

endTheory("Classical-Predicate-Logic");

// --- Proof functions ---

// implies false P
function proveExFalso(): Thm {
    const elim = subst(S("A", "x. x", "x", "P"), thm("for-all_elim"));
    return foldDefinition(elim, "false_def", "t. implies t P");
}

function proveExcludedMiddle(): Thm {
    const emAsImplication = impliesRefl(parse("not A")!);
    return foldDefinition(emAsImplication, "or_def", "t. t", ["A", "A", "B", "not A"]);
}

function proveOrIntro1(): Thm {
    const exFalsoB = subst(S("P", "B"), thm("ex-falso"));
    const weakenExFalso = modusPonens(
        subst(S("A", "implies false B", "B", "A"), thm("implies_1")),
        exFalsoB,
    );
    const falseToB = modusPonens(
        subst(S("A", "A", "B", "false", "C", "B"), thm("implies_2")),
        weakenExFalso,
    );
    const rawOrIntro = impliesExchange(falseToB);
    const expandedNotToOr = foldDefinition(
        rawOrIntro,
        "not_def",
        "t. implies A (implies t B)",
        ["A", "A"],
    );
    return foldDefinition(expandedNotToOr, "or_def", "t. implies A t", ["A", "A", "B", "B"]);
}

function proveOrIntro2(): Thm {
    const rawOrIntro = subst(S("A", "B", "B", "not A"), thm("implies_1"));
    return foldDefinition(rawOrIntro, "or_def", "t. implies B t", ["A", "A", "B", "B"]);
}

function proveOrElim(): Thm {
    const A = tyAtom("A");
    const B = tyAtom("B");
    const C = tyAtom("C");
    const falseTy = tyAtom("false");
    const AC = tyImp(A, C);
    const BC = tyImp(B, C);
    const rawOr = tyImp(tyImp(A, falseTy), B);
    const notC = tyImp(C, falseTy);
    const rawOrElim = provePureImplication(
        tyImp(AC, tyImp(BC, tyImp(rawOr, tyImp(notC, falseTy)))),
        lam("ac", AC, lam("bc", BC, lam("o", rawOr, lam("nc", notC,
            app(v("nc"), app(v("bc"), app(v("o"),
                lam("a", A, app(v("nc"), app(v("ac"), v("a")))),
            ))),
        )))),
    );
    const rawOrElimToExpandedOr = foldDefinition(
        rawOrElim,
        "not_def",
        "t. implies (implies A C) (implies (implies B C) (implies (implies t B) (implies (implies C false) false)))",
        ["A", "A"],
    );
    const rawOrElimToOr = foldDefinition(
        rawOrElimToExpandedOr,
        "or_def",
        "t. implies (implies A C) (implies (implies B C) (implies t (implies (implies C false) false)))",
        ["A", "A", "B", "B"],
    );
    const orElimToExpandedNotNotC = foldDefinition(
        rawOrElimToOr,
        "not_def",
        "t. implies (implies A C) (implies (implies B C) (implies (or A B) (implies t false)))",
        ["A", "C"],
    );
    const orElimToNotNotC = foldDefinition(
        orElimToExpandedNotNotC,
        "not_def",
        "t. implies (implies A C) (implies (implies B C) (implies (or A B) t))",
        ["A", "not C"],
    );
    const dneC = subst(S("A", "C"), thm("double-negation-elim"));
    const orNotNotCToOrC = modusPonens(
        subst(S("A", "or A B", "B", "not (not C)", "C", "C"), thm("implies_2")),
        applyInContext(dneC, "or A B"),
    );
    const bcOrNotNotCToBcOrC = modusPonens(
        subst(
            S("A", "implies B C", "B", "implies (or A B) (not (not C))", "C", "implies (or A B) C"),
            thm("implies_2"),
        ),
        applyInContext(orNotNotCToOrC, "implies B C"),
    );
    return conditionalModusPonens(applyInContext(bcOrNotNotCToBcOrC, "implies A C"), orElimToNotNotC);
}

function proveAndIntro(): Thm {
    const A = tyAtom("A");
    const B = tyAtom("B");
    const falseTy = tyAtom("false");
    const rawAndIntro = provePureImplication(
        tyImp(A, tyImp(B, tyImp(tyImp(A, tyImp(B, falseTy)), falseTy))),
        lam("a", A, lam("b", B, lam("h", tyImp(A, tyImp(B, falseTy)),
            app(app(v("h"), v("a")), v("b")),
        ))),
    );
    const rawAndIntroToExpandedNot = foldDefinition(
        rawAndIntro,
        "not_def",
        "t. implies A (implies B (implies (implies A t) false))",
        ["A", "B"],
    );
    const rawAndIntroToExpandedAnd = foldDefinition(
        rawAndIntroToExpandedNot,
        "not_def",
        "t. implies A (implies B t)",
        ["A", "implies A (not B)"],
    );
    return foldDefinition(rawAndIntroToExpandedAnd, "and_def", "t. implies A (implies B t)", ["A", "A", "B", "B"]);
}

function proveAndElim1(): Thm {
    const notA = parse("implies A false")!;
    const expandedAnd = parse("implies (implies A (not B)) false")!;

    const exFalsoNotB = subst(S("P", "not B"), thm("ex-falso"));
    const falseToNotB = modusPonens(
        subst(S("A", "implies false (not B)", "B", "A"), thm("implies_1")),
        exFalsoNotB,
    );
    const notAToAImpliesNotB = modusPonens(
        subst(S("A", "A", "B", "false", "C", "not B"), thm("implies_2")),
        falseToNotB,
    );
    const notAToExpandedAndFalse = conditionalModusPonens(
        applyInContext(impliesExchange(impliesRefl(expandedAnd)), notA),
        conditionalModusPonens(applyInContext(notAToAImpliesNotB, notA), impliesRefl(notA)),
    );
    const expandedAndToExpandedNotNotA = impliesExchange(notAToExpandedAndFalse);
    const expandedAndToExpandedNotA = foldDefinition(
        expandedAndToExpandedNotNotA,
        "not_def",
        "t. implies (implies (implies A (not B)) false) (implies t false)",
        ["A", "A"],
    );
    const expandedAndToNotNotA = foldDefinition(
        expandedAndToExpandedNotA,
        "not_def",
        "t. implies (implies (implies A (not B)) false) t",
        ["A", "not A"],
    );
    const expandedAndToA = impliesTrans(
        expandedAndToNotNotA,
        subst(S("A", "A"), thm("double-negation-elim")),
    );
    const andToA = foldDefinition(
        expandedAndToA,
        "not_def",
        "t. implies t A",
        ["A", "implies A (not B)"],
    );
    return foldDefinition(andToA, "and_def", "t. implies t A", ["A", "A", "B", "B"]);
}

function proveAndElim2(): Thm {
    const notB = parse("not B")!;
    const expandedAnd = parse("implies (implies A (not B)) false")!;

    const expandedNotBToAImpliesExpandedNotB = subst(S("A", "implies B false", "B", "A"), thm("implies_1"));
    const notBToExpandedNotB = foldDefinition(
        expandedNotBToAImpliesExpandedNotB,
        "not_def",
        "t. implies t (implies A (implies B false))",
        ["A", "B"],
    );
    const notBToAImpliesNotB = foldDefinition(
        notBToExpandedNotB,
        "not_def",
        "t. implies (not B) (implies A t)",
        ["A", "B"],
    );
    const notBToExpandedAndFalse = conditionalModusPonens(
        applyInContext(impliesExchange(impliesRefl(expandedAnd)), notB),
        notBToAImpliesNotB,
    );
    const expandedAndToExpandedNotNotB = impliesExchange(notBToExpandedAndFalse);
    const expandedAndToNotNotB = foldDefinition(
        expandedAndToExpandedNotNotB,
        "not_def",
        "t. implies (implies (implies A (not B)) false) t",
        ["A", "not B"],
    );
    const expandedAndToB = impliesTrans(
        expandedAndToNotNotB,
        subst(S("A", "B"), thm("double-negation-elim")),
    );
    const andToB = foldDefinition(
        expandedAndToB,
        "not_def",
        "t. implies t B",
        ["A", "implies A (not B)"],
    );
    return foldDefinition(andToB, "and_def", "t. implies t B", ["A", "A", "B", "B"]);
}

function proveEquivIntro(): Thm {
    const rawIntro = subst(S("A", "implies A B", "B", "implies B A"), thm("and_intro"));
    return foldDefinition(
        rawIntro,
        "equiv_def",
        "t. implies (implies A B) (implies (implies B A) t)",
        ["A", "A", "B", "B"],
    );
}

function proveEquivElim1(): Thm {
    const rawElim = subst(S("A", "implies A B", "B", "implies B A"), thm("and_elim_1"));
    return foldDefinition(rawElim, "equiv_def", "t. implies t (implies A B)", ["A", "A", "B", "B"]);
}

function proveEquivElim2(): Thm {
    const rawElim = subst(S("A", "implies A B", "B", "implies B A"), thm("and_elim_2"));
    return foldDefinition(rawElim, "equiv_def", "t. implies t (implies B A)", ["A", "A", "B", "B"]);
}

function proveExistsIntro(): Thm {
    const forAllElimNotA = subst(S("A", "y. not A[y]", "x", "x"), thm("for-all_elim"));
    const notAxToExpandedNotAx = transportDefinitionRenamed("not_def", {
        rename: ["A", "Q"],
        instantiate: ["Q", "A[x]"],
    });
    const aToExpandedNotForAll = impliesExchange(impliesTrans(forAllElimNotA, notAxToExpandedNotAx));
    const expandedNotForAllToNotForAll = transportDefinitionRenamed("not_def", {
        rename: ["A", "Q"],
        instantiate: ["Q", "for-all (x. not A[x])"],
        symmetric: true,
    });
    const aToNotForAll = impliesTrans(aToExpandedNotForAll, expandedNotForAllToNotForAll);
    const notForAllToExists = transportDefinitionRenamed("exists_def", {
        rename: ["A", "z. B[z]"],
        instantiate: ["B", "z. A[z]"],
        symmetric: true,
    });
    return impliesTrans(aToNotForAll, notForAllToExists);
}

function proveExistsElim(): Thm {
    const A = tyAtom("A");
    const C = tyAtom("C");
    const falseTy = tyAtom("false");
    const rawContrapositive = provePureImplication(
        tyImp(tyImp(A, C), tyImp(tyImp(C, falseTy), tyImp(A, falseTy))),
        lam("ac", tyImp(A, C), lam("nc", tyImp(C, falseTy), lam("a", A,
            app(v("nc"), app(v("ac"), v("a"))),
        ))),
    );
    const contrapositiveExpanded = foldDefinition(
        subst(S("A", "A[x]", "C", "C"), rawContrapositive),
        "not_def",
        "t. implies (implies A[x] C) (implies t (implies A[x] false))",
        ["A", "C"],
    );
    const expandedNotAxToNotAx = transportDefinitionRenamed("not_def", {
        rename: ["A", "Q"],
        instantiate: ["Q", "A[x]"],
        symmetric: true,
    });
    const contrapositive = conditionalImpliesTrans(
        contrapositiveExpanded,
        applyInContext(expandedNotAxToNotAx, "implies A[x] C"),
    );
    const forAllNotAImplications = forAllIntroFrom(
        modusPonens(contrapositive, assume("implies A[x] C")),
        "y. implies (not C) (not A[y])",
        "implies A[x] C",
        "x. implies A[x] C",
    );
    const forAllNotAFromNotC = modusPonens(
        subst(S("A", "not C", "B", "y. not A[y]"), thm("for-all_distr")),
        forAllNotAImplications,
    );
    const existsToExpandedExists = impliesTrans(
        transportDefinitionRenamed("exists_def", {
            rename: ["A", "z. B[z]"],
            instantiate: ["B", "z. A[z]"],
        }),
        transportDefinitionRenamed("not_def", {
            rename: ["A", "Q"],
            instantiate: ["Q", "for-all (x. not A[x])"],
        }),
    );
    const expandedExists = modusPonens(existsToExpandedExists, assume("exists (x. A[x])"));
    const notCToFalse = conditionalModusPonens(applyInContext(expandedExists, "not C"), forAllNotAFromNotC);
    const notCToC = impliesTrans(notCToFalse, subst(S("P", "C"), thm("ex-falso")));
    const orElimC = subst(S("A", "C", "B", "not C", "C", "C"), thm("or_elim"));
    return modusPonens(
        modusPonens(
            modusPonens(orElimC, impliesRefl(parse("C")!)),
            notCToC,
        ),
        subst(S("A", "C"), thm("excluded-middle")),
    );
}
