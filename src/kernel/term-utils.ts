import { assertNever, nat } from "things";
import { TermKind, Terms } from "./terms.js";

export function destNormalVariableTemplate<Id, Term>(terms : Terms<Id, Term>, term : Term) : 
    [Id, nat] | undefined 
{
    const [binders, body] = terms.destTemplate(term);
    const termKind = terms.termKindOf(body);
    if (termKind  !== TermKind.varapp) return undefined;
    const [id, args] = terms.destVarApp(body);
    if (args.length !== binders.length) return undefined;
    for (const [i, arg] of args.entries()) {
        if (terms.termKindOf(arg) !== TermKind.bound) return undefined;
        const index = terms.destBoundVar(arg);
        if (i !== index) return undefined;
    }
    return [id, args.length];
}

export function isNormalHead<Id, Term>(terms : Terms<Id, Term>, term : Term) : boolean 
{
    if (terms.termKindOf(term) !== TermKind.absapp) return false;
    const absapp = terms.destAbsApp(term);
    const vars : [Id, nat][] = []
    for (const [_, args] of absapp) {
        for (const arg of args) {
            const v = destNormalVariableTemplate(terms, arg);
            if (v === undefined) return false;
            if (vars.findIndex(w => terms.ids.equal(v[0], w[0]) && v[1] === w[1]) >= 0) 
                return false;
            vars.push(v);
        }
    }
    return true;
}

export function isFreeWithArityZero<Id, Term>(terms : Terms<Id, Term>, xs : Id[], term : Term)
    : boolean 
{
    if (xs.length === 0) return false;
    function eq(y : Id) : boolean {
        for (const x of xs) {
            if (terms.ids.equal(x, y)) return true;
        }
        return false;
    }
    function isFree(term : Term) : boolean {
        const termKind = terms.termKindOf(term);
        switch (termKind) {
            case TermKind.bound: return false;
            case TermKind.template: return isFree(terms.destTemplate(term)[1]);
            case TermKind.varapp: {
                const [y, args] = terms.destVarApp(term);
                if (args.length === 0 && eq(y)) {
                    return true;
                } 
                for (const arg of args) {
                    if (isFree(arg)) return true;
                }
                return false;
            }
            case TermKind.absapp: {
                const absapp = terms.destAbsApp(term);
                for (const [_, args] of absapp) {
                    for (const arg of args) {
                        if (isFree(arg)) return true;
                    }
                }
                return false;
            }
            case TermKind.template: {
                const [_, body] = terms.destTemplate(term);
                return isFree(body);
            }
            default: assertNever(termKind);
        }
    }
    return isFree(term);
}
