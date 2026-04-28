import { Term, simpleSubstNoDangling } from "../kernel/index.js";
import { conclOf, infer, parse, S, subst, terms, Thm, thm } from "../workbench.js";
import { impliesRefl } from "../theories/Implication.theory.js";
import { destEquals } from "../theories/Pure-Equality.theory.js";

function instantiateUnaryTemplate(template: Term, arg: Term): Term {
    const t = terms();
    const [binders, body] = t.destTemplate(template);
    if (binders.length !== 1)
        throw new Error("transportProvenEquality: expected a unary template.");
    return simpleSubstNoDangling(t, 0, body, [arg]);
}

function mkImplicationTemplate(source: Term, template: Term): Term {
    const t = terms();
    const [binders, body] = t.destTemplate(template);
    if (binders.length !== 1)
        throw new Error("transportProvenEquality: expected a unary template.");
    return t.mkTemplate(binders, t.mkAbsApp([[t.mkId("implies"), [source, body]]]));
}

export function transportProvenEquality(equality: Thm, equalityTemplate: string | Term = "t. t"): Thm {
    const template = parse(equalityTemplate);
    if (template === undefined)
        throw new Error("transportProvenEquality: cannot parse equality template.");
    const [lhs, rhs] = destEquals(conclOf(equality));
    const source = instantiateUnaryTemplate(template, lhs);
    const step = subst(
        S("x", lhs, "y", rhs, "A", mkImplicationTemplate(source, template)),
        thm("pure_equals_subst"),
    );
    return infer(infer(step, equality), impliesRefl(source));
}

export function equalityAsImplication(equality: Thm): Thm {
    return transportProvenEquality(equality, "t. t");
}
