import { Term } from "../kernel/index.js";
import { beginTheory, declare, axiom, endTheory, thm, S, subst, Thm, conclOf, terms, infer, assume, have, parse } from "../workbench.js";

// This logic is also called "Minimal Implicative Logic", or "Positive Implicative Logic"

beginTheory();
declare("implies A B")
axiom("modus-ponens", "B", ["implies A B", "A"])
axiom("implies_1", "implies A (implies B A)")
axiom("implies_2", "implies (implies A (implies B C)) (implies (implies A B) (implies A C))")
have("implies_weakening", "implies B A", ["A"], proveWeakening());
have("conditional-modus-ponens", "implies C B", ["implies C (implies A B)", "implies C A"], proveConditionalModusPonens());
have("implies_refl", "implies A A", [], proveRefl());
have("implies_trans", "implies A C", ["implies B C", "implies A B"], proveTrans());
have("implies_exchange", "implies B (implies A C)", ["implies A (implies B C)"], proveExchange());
have("implies_contraction", "implies A B", ["implies A (implies A B)"], proveContraction());
endTheory("Implication");

//exportTeX("Implication");

function proveWeakening() : Thm {
    const thm1 = thm("implies_1");
    return modusPonens(thm1, assume("A"));
}

function proveRefl() : Thm {
    const thm1 = subst(S("B", "A"), thm("implies_1"))
    const thm2 = subst(S("B", "implies A A"), thm("implies_1"))
    const thm3 = subst(S("B", "implies A A", "C", "A"), thm("implies_2"))
    const thm4 = modusPonens(thm3, thm2);
    return modusPonens(thm4, thm1);
}

function proveConditionalModusPonens() : Thm {
    const thm1 = subst(S("A", "C", "B", "A", "C", "B"), thm("implies_2"));
    const AB = assume("implies C (implies A B)");
    const thm2 = modusPonens(thm1, AB);
    const A = assume("implies C A");
    return modusPonens(thm2, A);
}

function proveTrans() : Thm {
    const B = assume("implies A B");
    const BC = subst(S("B", "A", "A", "implies B C"), thm("implies_weakening"));
    return conditionalModusPonens(BC, B);
}

export function destImplies(implication : Term) : [Term, Term] {
    const absapp = terms().destAbsApp(implication);
    if (absapp.length !== 1) throw new Error("destImplies");
    const [id, args] = absapp[0];
    if (id !== "implies" || args.length !== 2) throw new Error("destImplies");
    return [args[0], args[1]];
}

export function modusPonens(implication : Thm, assumption : Thm) : Thm {
    const mp = thm("modus-ponens");
    const [A, B] = destImplies(conclOf(implication));
    const general = subst(S("A", A, "B", B), mp);
    return infer(infer(general, implication), assumption);   
}

export function impliesTrans(AB : Thm, BC : Thm) : Thm {
    const [A, B] = destImplies(conclOf(AB));
    const [_, C] = destImplies(conclOf(BC));
    return infer(infer(subst(S("A", A, "B", B, "C", C), thm("implies_trans")), AB), BC);
}

export function impliesRefl(A : Term) : Thm {
    return subst(S("A", A), thm("implies_refl"));
}

export function conditionalModusPonens(implication : Thm, assumption : Thm) : Thm {
    const mp = thm("conditional-modus-ponens");
    const [C, AB] = destImplies(conclOf(implication));
    const [A, B] = destImplies(AB);
    const general = subst(S("C", C, "A", A, "B", B), mp);
    return infer(infer(general, implication), assumption);
}

function proveExchange() : Thm {
    const thm1 = assume("implies A (implies B C)");
    const thm2 = subst(S("A", "B", "B", "A"), thm("implies_1"));
    const thm4 = modusPonens(thm("implies_2"), thm1);
    return impliesTrans(thm2, thm4);
}

export function impliesExchange(implication : Thm) : Thm {
    const [A, BC] = destImplies(conclOf(implication));
    const [B, C] = destImplies(BC);
    return infer(subst(S("A", A, "B", B, "C", C), thm("implies_exchange")), implication);
}

function proveContraction() : Thm {
    const assm = assume("implies A (implies A B)");
    return modusPonens(modusPonens(impliesExchange(subst(S("B", "A", "C", "B"), thm("implies_2"))),
        thm("implies_refl")), assm);
}

export function weaken(th : Thm, hyp : string | Term) : Thm {
    const h = typeof hyp === "string" ? parse(hyp)! : hyp;
    return modusPonens(subst(S("A", conclOf(th), "B", h), thm("implies_1")), th);
}

export function applyInContext(th : Thm, hyp : string | Term) : Thm {
    return weaken(th, hyp);
}

export function mapConsequent(AB : Thm, BC : Thm) : Thm {
    return impliesTrans(AB, BC);
}

// implies H (implies A B) + implies H (implies B C) → implies H (implies A C)
export function conditionalImpliesTrans(hAB : Thm, hBC : Thm) : Thm {
    const [H, implAB] = destImplies(conclOf(hAB));
    const [A, B] = destImplies(implAB);
    const [_, implBC] = destImplies(conclOf(hBC));
    const [__, C] = destImplies(implBC);
    // implies (implies B C) (implies (implies A B) (implies A C))
    // = K >> S where K weakens and S distributes
    const k = subst(S("A", implBC, "B", A), thm("implies_1"));
    const s = subst(S("A", A, "B", B, "C", C), thm("implies_2"));
    const chain = impliesTrans(k, s);
    // implies H (implies (implies A B) (implies A C))
    const hToStep = impliesTrans(hBC, chain);
    // S combinator to combine with hAB
    const [___, inner] = destImplies(conclOf(hToStep));
    const [innerA, innerC] = destImplies(inner);
    return modusPonens(modusPonens(
        subst(S("A", H, "B", innerA, "C", innerC), thm("implies_2")),
        hToStep), hAB);
}

export function conditionalMapConsequent(hAB : Thm, hBC : Thm) : Thm {
    return conditionalImpliesTrans(hAB, hBC);
}
