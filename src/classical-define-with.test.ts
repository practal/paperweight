import { assertCrashT, assertEqT, Test } from "things";
import "./theories/Classical-Predicate-Logic.theory.js";
import { modusPonens } from "./theories/Implication.theory.js";
import { beginTheory, conclOf, defineWith, display, endTheory, have, includeTheory, S, subst, thm } from "./workbench.js";

Test(() => {
    assertCrashT(() => {
        beginTheory();
        includeTheory("Classical-Predicate-Logic");
        defineWith("x y. equiv x y", "same-truth A", "A");
    });
}, "defineWith via equiv requires reflexivity theorem");

Test(() => {
    beginTheory();
    includeTheory("Classical-Predicate-Logic");

    const intro = subst(S("A", "A", "B", "A"), thm("equiv_intro"));
    const refl = thm("implies_refl");
    const step = modusPonens(intro, refl);
    const equivRefl = modusPonens(step, refl);
    have("equiv_refl", "equiv A A", [], equivRefl);

    defineWith("x y. equiv x y", "same-truth A", "A");
    assertEqT(display(conclOf(thm("same-truth_def"))), "equiv (same-truth A) A");

    endTheory("Classical-DefineWith");
}, "defineWith via equiv in Classical Predicate Logic");
