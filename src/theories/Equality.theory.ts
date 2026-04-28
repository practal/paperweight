import { Term } from "../kernel/default-terms.js";
import { simpleSubstNoDangling } from "../kernel/index.js";
import { beginTheory, declare, axiom, endTheory, conclOf, S, subst, terms, Thm, thm, parse, have, includeTheory } from "../workbench.js";
import "./Implication.theory.js";
import { modusPonens, conditionalModusPonens, impliesTrans, impliesExchange, destImplies, weaken } from "./Implication.theory.js";

beginTheory();
includeTheory("Implication");
declare("equals x y");
axiom("equals_refl", "equals x x");
axiom("equals_subst", "implies (equals x y) (implies A[x] A[y])");
have("equals_sym", "implies (equals x y) (equals y x)", [], proveSym());
have("equals_trans", "implies (equals x y) (implies (equals y z) (equals x z))", [], proveEqualsTrans());
have("equals_cong", "implies (equals x y) (equals F[x] F[y])", [], proveEqualsCong());
endTheory("Equality");

export function destEquals(implication : Term) : [Term, Term] {
    const absapp = terms().destAbsApp(implication);
    if (absapp.length !== 1) throw new Error("destEquals");
    const [id, args] = absapp[0];
    if (id !== "equals" || args.length !== 2) throw new Error("destEquals");
    return [args[0], args[1]];
}

export function substEquals(eq : Thm) : Thm {
    const [x, y] = destEquals(conclOf(eq));
    return modusPonens(subst(S("x", x, "y", y), thm("equals_subst")), eq);
}

function proveSym() : Thm {
    // implies (equals x y) (implies (equals x x) (equals y x))
    const step1 = subst(S("A", "y. equals y x"), thm("equals_subst"));
    // implies (equals x x) (implies (equals x y) (equals x x))  — from implies_1
    // then modusPonens with equals_refl: implies (equals x y) (equals x x)
    const weakRefl = modusPonens(subst(S("A", "equals x x", "B", "equals x y"), thm("implies_1")), thm("equals_refl"));
    // conditionalModusPonens: implies (equals x y) (equals y x)
    return conditionalModusPonens(step1, weakRefl);
}

function proveEqualsTrans() : Thm {
    // Rename x→y, y→z in equals_subst and set A[t] = equals x t simultaneously:
    //   implies (equals y z) (implies (equals x y) (equals x z))
    const step = subst(S("x", "y", "y", "z", "A", "(t. equals x t)"), thm("equals_subst"));
    // exchange to get: implies (equals x y) (implies (equals y z) (equals x z))
    return impliesExchange(step);
}

function proveEqualsCong() : Thm {
    // equals_subst with A[t] = equals F[x] F[t]:
    //   implies (equals x y) (implies (equals F[x] F[x]) (equals F[x] F[y]))
    const step = subst(S("A", "(t. equals F[x] F[t])"), thm("equals_subst"));
    // weaken refl: implies (equals x y) (equals F[x] F[x])
    const refl = subst(S("x", parse("F[x]")!), thm("equals_refl"));
    const weakRefl = weaken(refl, "equals x y");
    // conditionalModusPonens: implies (equals x y) (equals F[x] F[y])
    return conditionalModusPonens(step, weakRefl);
}

export function equalsSym(th : Thm) : Thm {
    const [x, y] = destEquals(conclOf(th));
    return modusPonens(subst(S("x", x, "y", y), thm("equals_sym")), th);
}

export function equalsRefl(t : string | Term) : Thm {
    const tm = parse(t);
    if (tm === undefined) throw new Error("equalsRefl: cannot parse term");
    return subst(S("x", tm), thm("equals_refl"));
}

// Helper: build template "u. equals a u" from term a
function mkEqTemplate(a : Term) : Term {
    const t = terms();
    const binderId = t.mkId("_v");
    return t.mkTemplate([binderId], t.mkAbsApp([[t.mkId("equals"), [a, t.mkBoundVar(0)]]]));
}

// Helper: build "congruence rule" implies (equals a b) (equals f[a] f[b]) from template
function congrRule(a : Term, b : Term, template : string) : Thm {
    const t = terms();
    const tmpl = parse(template);
    if (tmpl === undefined) throw new Error("congrRule: cannot parse template");
    const [binders, body] = t.destTemplate(tmpl);
    const fa = simpleSubstNoDangling(t, 0, body, [a]);
    const eqId = t.mkId("equals");
    const aTemplate = t.mkTemplate(binders, t.mkAbsApp([[eqId, [fa, body]]]));
    // equals_subst[x→a, y→b, A→"u. equals fa f[u]"]:
    //   implies (equals a b) (implies (equals fa fa) (equals fa fb))
    const step = subst(S("x", a, "y", b, "A", aTemplate), thm("equals_subst"));
    // weaken refl: implies (equals a b) (equals fa fa)
    const faRefl = subst(S("x", fa), thm("equals_refl"));
    const [eqAB, _2] = destImplies(conclOf(step));
    const weakRefl = modusPonens(
        subst(S("A", conclOf(faRefl), "B", eqAB), thm("implies_1")), faRefl);
    // conditionalModusPonens: implies (equals a b) (equals fa fb)
    return conditionalModusPonens(step, weakRefl);
}

// equals a b + equals b c → equals a c
export function equalsTrans(eq1 : Thm, eq2 : Thm) : Thm {
    const [a, _] = destEquals(conclOf(eq1));
    return modusPonens(subst(S("A", mkEqTemplate(a)), substEquals(eq2)), eq1);
}

// equals a b + template "t. f[t]" → equals f[a] f[b]
export function congr(eq : Thm, template : string) : Thm {
    const [a, b] = destEquals(conclOf(eq));
    return modusPonens(congrRule(a, b, template), eq);
}

// implies H (equals a b) + implies H (equals b c) → implies H (equals a c)
export function conditionalEqualsTrans(eq1 : Thm, eq2 : Thm) : Thm {
    const [_, eqAB] = destImplies(conclOf(eq1));
    const [a, __] = destEquals(eqAB);
    const [___, eqBC] = destImplies(conclOf(eq2));
    const [b, c] = destEquals(eqBC);
    // equals_subst[A = u. equals a u]: implies (equals b c) (implies (equals a b) (equals a c))
    const transRule = subst(S("x", b, "y", c, "A", mkEqTemplate(a)), thm("equals_subst"));
    // implies H (implies (equals a b) (equals a c))
    const hToTrans = impliesTrans(eq2, transRule);
    // conditionalModusPonens: implies H (equals a c)
    return conditionalModusPonens(hToTrans, eq1);
}

// implies H (equals a b) + template "t. f[t]" → implies H (equals f[a] f[b])
export function conditionalCongr(eq : Thm, template : string) : Thm {
    const [_, eqAB] = destImplies(conclOf(eq));
    const [a, b] = destEquals(eqAB);
    return impliesTrans(eq, congrRule(a, b, template));
}
