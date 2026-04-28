import { HashMap, nat, assertNever, Hash, Thing } from "things";
import { Terms, TermKind } from "./terms.js";

export type FreeVars<Id> = HashMap<Id, Set<nat>>  // no empty sets allowed as values

export function addFreeVar<Id>(freeVars : FreeVars<Id>, id : Id, arity : nat) {
    const arities = freeVars.get(id);
    if (arities === undefined) {
        freeVars.put(id, new Set([arity]))
    } else {
        arities.add(arity);
    }
}

export function emptyFreeVars<Id>(ids : Hash<Id>) : FreeVars<Id> {
    return new HashMap(ids);
}

export function addFreeVarsOf<Id, Term>(terms : Terms<Id, Term>, term : Term, 
    freeVars : FreeVars<Id>) 
{
    function collect(term : Term) {
        const kind = terms.termKindOf(term);
        switch (kind) {
            case TermKind.varapp: {
                const [id, args] = terms.destVarApp(term);
                addFreeVar(freeVars, id, args.length);
                for (const arg of args) {
                    collect(arg);
                }
                break;
            }
            case TermKind.absapp: {
                for (const [id, args] of terms.destAbsApp(term)) {
                    for (const arg of args) {
                        collect(arg);
                    }
                }
                break;
            }
            case TermKind.bound: {
                break;
            }
            case TermKind.template: {
                collect(terms.destTemplate(term)[1]);
                break;
            }
            default: assertNever(kind);
        }
    }
    collect(term);
    return freeVars;
}

export function freeVarsOf<Id, Term>(terms : Terms<Id, Term>, term : Term) : FreeVars<Id> 
{
    const freeVars = emptyFreeVars(terms.ids);
    addFreeVarsOf(terms, term, freeVars);
    return freeVars;
}

export function subtractFreeVars<Id>(fromFreeVars : FreeVars<Id>, freeVars : FreeVars<Id>)
{
    for (const [id, arities] of freeVars) {
        const fromArities = fromFreeVars.get(id);
        if (fromArities !== undefined) {
            for (const arity of arities) {
                fromArities.delete(arity);
            }
            if (fromArities.size === 0) fromFreeVars.remove(id);
        }
    }
}

export function displayFreeVar<Id>(ids : Thing<Id>, freeVar : [Id, nat]) : string {
    let d = ids.display(freeVar[0]);
    if (freeVar[1] === 0) return d;
    d += "[_";
    for (let i = 1; i < freeVar[1]; i++) d += ", _";
    return d + "]";
}

export function listFreeVars<Id>(freeVars : FreeVars<Id>) : [Id, nat][] {
    const list : [Id, nat][] = [];
    for (const [id, arities] of freeVars) {
        for (const arity of arities) {
            list.push([id, arity]);
        }
    }
    return list;
}


