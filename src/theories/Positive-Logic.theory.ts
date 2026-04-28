import { axiom, beginTheory, declare, endTheory, have, includeTheory, S, subst, Thm, thm } from "../workbench.js";
import "./Implication.theory.js";
import { modusPonens, conditionalModusPonens, impliesTrans } from "./Implication.theory.js";

beginTheory();
includeTheory("Implication");
declare("and A B");
declare("or A B");
axiom("or-intro_1", "implies A (or A B)");
axiom("or-intro_2", "implies B (or A B)");
axiom("or-elim", "implies (implies A C) (implies (implies B C) (implies (or A B) C))");
axiom("and-elim_1", "implies (and A B) A");
axiom("and-elim_2", "implies (and A B) B");
axiom("and-intro", "implies A (implies B (and A B))");
have("and-comm", "implies (and A B) (and B A)", [], proveAndComm());
have("or-comm", "implies (or A B) (or B A)", [], proveOrComm());
endTheory("Positive-Logic");

function proveAndComm() : Thm {
    const elim2 = thm("and-elim_2");
    const elim1 = thm("and-elim_1");
    const intro = subst(S("A", "B", "B", "A"), thm("and-intro"));
    const step4 = impliesTrans(elim2, intro);
    return conditionalModusPonens(step4, elim1);
}

function proveOrComm() : Thm {
    const intro2 = subst(S("B", "A", "A", "B"), thm("or-intro_2"));
    const intro1 = subst(S("A", "B", "B", "A"), thm("or-intro_1"));
    const elim = subst(S("C", "or B A"), thm("or-elim"));
    const step4 = modusPonens(elim, intro2);
    return modusPonens(step4, intro1);
}