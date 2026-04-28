import { assertNever, Data, HashMap, int, nat, RedBlackMap } from "things";
import { Signature } from "./signature.js";
import { TermKind, Terms } from "./terms.js";
import { validateTerm } from "./validate.js";

export type Subst<Id, Term> = RedBlackMap<Id, RedBlackMap<nat, Term>>

export function newSubst<Id, Term>(ids : Data<Id>) : Subst<Id, Term> {
    return RedBlackMap(ids);
}

export function addSubst<Id, Term>(subst : Subst<Id, Term>, id : Id, arity : nat, term : Term) 
    : Subst<Id, Term>
{
    let m = subst.get(id);
    if (m === undefined) {
        const m = RedBlackMap<nat, Term>(nat, [[arity, term]]);
        return subst.set(id, m);
    } else {
        m = m.set(arity, term);
        return subst.set(id, m);
    }
}

export function lookupInSubst<Id, Term>(subst : Subst<Id, Term>, id : Id, arity : nat) 
    : Term | undefined 
{
    const m = subst.get(id);
    if (m === undefined) return undefined;
    return m.get(arity);
}

export function validateSubst<Id, Term>(sig : Signature<Id>, terms : Terms<Id, Term>, 
    subst : Subst<Id, Term>) 
{
    for (const [x, m] of subst) {
        for (const [arity, t] of m) {
            const [binders, _] = terms.destTemplate(t);
            if (binders.length !== arity) 
                throw new Error("Cannot validate substitution for variable " + 
                    terms.ids.display(x) + " at arity " + arity + 
                    ", wrong template arity " + binders.length);
            validateTerm(sig, terms, t);
        }
    }
}

export function liftTerm<Id, Term>(terms : Terms<Id, Term>, level : nat, z : int, term : Term) : Term {

    function lift(level : nat, term : Term) : Term {
        const termKind = terms.termKindOf(term);
        switch (termKind) {
            case TermKind.bound: {
                const index = terms.destBoundVar(term);
                if (index < level) return term;
                else return terms.mkBoundVar(index + z);
            }
            case TermKind.varapp: {
                const [id, args] = terms.destVarApp(term);
                return terms.mkVarApp(id, args.map(a => lift(level, a)));
            }
            case TermKind.absapp: {
                const absapp = terms.destAbsApp(term);
                return terms.mkAbsApp(absapp.map(([id, args]) => 
                    [id, args.map(a => lift(level, a))]));
            }
            case TermKind.template: {
                const [binders, body] = terms.destTemplate(term);
                return terms.mkTemplate(binders, lift(level + binders.length, body));
            }
            default: assertNever(termKind);
        }
    }
    
    if (z === 0) return term; 
    return lift(level, term);
} 

function simpleSubst<Id, Term>(terms : Terms<Id, Term>, level : nat, 
    term : Term, args : Term[]) : Term 
{
    function subst(level : nat, term : Term, args : Term[]) : Term {
        const termKind = terms.termKindOf(term);
        switch (termKind) {
            case TermKind.bound: {
                const index = terms.destBoundVar(term);
                if (index >= level && index < level + args.length) {
                    return args[index - level];
                } else return term;
            }
            case TermKind.absapp: {
                const absapp = terms.destAbsApp(term);
                return terms.mkAbsApp(absapp.map(([id, params]) => [id, params.map(a => 
                    subst(level, a, args))]));
            }
            case TermKind.varapp: {
                const [x, params] = terms.destVarApp(term);
                return terms.mkVarApp(x, params.map(a => subst(level, a, args)));
            }
            case TermKind.template: {
                const [binders, body] = terms.destTemplate(term);
                const k = binders.length;
                const newBody = subst(level + k, body, args.map(a => liftTerm(terms, 0, k, a)));
                return terms.mkTemplate(binders, newBody);
            }
            default: assertNever(termKind);
        }
    }
        
    return subst(level, term, args);
}

function simpleApply<Id, Term>(terms : Terms<Id, Term>, 
    term : Term, args : Term[]) : Term
{
    function apply(term : Term, args : Term[]) : Term {
        const [binders, body] = terms.destTemplate(term);
        const n = binders.length;
        if (n !== args.length) 
            throw new Error("applySubst: wrong number of arguments");
        const liftedArgs = args.map(a => liftTerm(terms, 0, n, a));
        const t = simpleSubst(terms, 0, body, liftedArgs);
        return liftTerm(terms, 0, -n, t);
    }
        
    return apply(term, args);
}

export function applyRegularSubst<Id, Term>(terms : Terms<Id, Term>, 
    term : Term, subst : Subst<Id, Term>) : Term
{
    function apply(term : Term) : Term {
        const termKind = terms.termKindOf(term);
        switch (termKind) {
            case TermKind.bound: return term;
            case TermKind.varapp: {
                const [x, args] = terms.destVarApp(term);
                const t = lookupInSubst(subst, x, args.length);
                const substitutedArgs = args.map(apply);
                if (t === undefined) {
                    return terms.mkVarApp(x, substitutedArgs);
                } else {
                    return simpleApply(terms, t, substitutedArgs);
                }
            }
            case TermKind.absapp: {
                const absapp = terms.destAbsApp(term);
                return terms.mkAbsApp(absapp.map(([id, args]) => [id, args.map(apply)]));
            }
            case TermKind.template: {
                const [binders, body] = terms.destTemplate(term);
                return terms.mkTemplate(binders, apply(body));
            }
        }
    }
    
    return apply(term);
}

export function substVars<Id, Term>(terms : Terms<Id, Term>, 
    boundVars : Map<nat, nat>, freeVars : HashMap<Id, nat>, term : Term) : Term 
{
    function subst(level : nat, term : Term) : Term {
        const termKind = terms.termKindOf(term);
        switch (termKind) {
            case TermKind.bound: {
                const index = terms.destBoundVar(term);
                if (index >= level) {
                    const b = boundVars.get(index - level);
                    if (b !== undefined) return terms.mkBoundVar(b + level);
                }
                return term;
            }
            case TermKind.varapp: {
                const [x, args] = terms.destVarApp(term);
                if (args.length === 0) {
                    const b = freeVars.get(x);
                    if (b !== undefined) return terms.mkBoundVar(b + level);
                }
                return terms.mkVarApp(x, args.map(t => subst(level, t)));
            }
            case TermKind.absapp: {
                const absapp = terms.destAbsApp(term);
                return terms.mkAbsApp(absapp.map(([id, args]) => 
                    [id, args.map(t => subst(level, t))]));
            }
            case TermKind.template: {
                const [binders, body] = terms.destTemplate(term);
                return terms.mkTemplate(binders, subst(level + binders.length, body));
            }
            default: assertNever(termKind);
        }
    }
    return subst(0, term);
}

// Here we require args to have no dangling indices.
export function simpleSubstNoDangling<Id, Term>(terms : Terms<Id, Term>, level : nat, 
    term : Term, args : Term[]) : Term 
{
    function subst(level : nat, term : Term) : Term {
        const termKind = terms.termKindOf(term);
        switch (termKind) {
            case TermKind.bound: {
                const index = terms.destBoundVar(term);
                if (index >= level && index < level + args.length) {
                    return args[index - level];
                } else return term;
            }
            case TermKind.absapp: {
                const absapp = terms.destAbsApp(term);
                return terms.mkAbsApp(absapp.map(([id, args]) => [id, args.map(a => 
                    subst(level, a))]));
            }
            case TermKind.varapp: {
                const [x, args] = terms.destVarApp(term);
                return terms.mkVarApp(x, args.map(a => subst(level, a)));
            }
            case TermKind.template: {
                const [binders, body] = terms.destTemplate(term);
                const k = binders.length;
                const newBody = subst(level + k, body);
                return terms.mkTemplate(binders, newBody);
            }
            default: assertNever(termKind);
        }
    }
    
    return subst(level, term);
}

