import { Term } from "../kernel/default-terms.js";
import { simpleSubstNoDangling } from "../kernel/index.js";
import { beginTheory, declare, axiom, endTheory, conclOf, S, subst, terms, Thm, thm, parse, have, infer, assume } from "../workbench.js";

beginTheory();
declare("equals x y");
axiom("pure_equals_refl", "equals x x");
axiom("pure_equals_subst", "A[y]", ["equals x y", "A[x]"]);
have("pure_equals_sym", "equals y x", ["equals x y"], proveSym());
have("pure_equals_trans", "equals x z", ["equals x y", "equals y z"], proveEqualsTrans());
have("pure_equals_cong", "equals F[x] F[y]", ["equals x y"], proveEqualsCong());
endTheory("Pure-Equality");

export function destEquals(equality : Term) : [Term, Term] {
    const absapp = terms().destAbsApp(equality);
    if (absapp.length !== 1) throw new Error("destEquals");
    const [id, args] = absapp[0];
    if (id !== "equals" || args.length !== 2) throw new Error("destEquals");
    return [args[0], args[1]];
}

export function substEquals(eq : Thm) : Thm {
    const [x, y] = destEquals(conclOf(eq));
    return infer(subst(S("x", x, "y", y), thm("pure_equals_subst")), eq);
}

function proveSym() : Thm {
    const step = subst(S("A", "y. equals y x"), thm("pure_equals_subst"));
    return infer(step, thm("pure_equals_refl"));
}

function proveEqualsTrans() : Thm {
    const step = subst(S("x", "y", "y", "z", "A", "(t. equals x t)"), thm("pure_equals_subst"));
    return infer(infer(step, assume("equals x y")), assume("equals y z"));
}

function proveEqualsCong() : Thm {
    const step = subst(S("A", "(t. equals F[x] F[t])"), thm("pure_equals_subst"));
    const refl = subst(S("x", parse("F[x]")!), thm("pure_equals_refl"));
    return infer(step, refl);
}

export function equalsSym(th : Thm) : Thm {
    const [x, y] = destEquals(conclOf(th));
    return infer(subst(S("x", x, "y", y), thm("pure_equals_sym")), th);
}

export function equalsRefl(t : string | Term) : Thm {
    const tm = parse(t);
    if (tm === undefined) throw new Error("equalsRefl: cannot parse term");
    return subst(S("x", tm), thm("pure_equals_refl"));
}

function congrRule(a : Term, b : Term, template : string) : Thm {
    const t = terms();
    const tmpl = parse(template);
    if (tmpl === undefined) throw new Error("congrRule: cannot parse template");
    const [binders, body] = t.destTemplate(tmpl);
    const fa = simpleSubstNoDangling(t, 0, body, [a]);
    const eqId = t.mkId("equals");
    const aTemplate = t.mkTemplate(binders, t.mkAbsApp([[eqId, [fa, body]]]));
    const step = subst(S("x", a, "y", b, "A", aTemplate), thm("pure_equals_subst"));
    const faRefl = subst(S("x", fa), thm("pure_equals_refl"));
    return infer(step, faRefl);
}

export function equalsTrans(eq1 : Thm, eq2 : Thm) : Thm {
    const [a, b] = destEquals(conclOf(eq1));
    const [_, c] = destEquals(conclOf(eq2));
    return infer(infer(subst(S("x", a, "y", b, "z", c), thm("pure_equals_trans")), eq1), eq2);
}

export function congr(eq : Thm, template : string) : Thm {
    const [a, b] = destEquals(conclOf(eq));
    return infer(congrRule(a, b, template), eq);
}
