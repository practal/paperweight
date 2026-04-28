import { arrayEqual, HashSet } from "things"
import { Terms } from "./terms.js"
import { Binder, Rule } from "./theory.js"
import { Subst } from "./subst.js"

export enum ProofKind {
    Axiom = "Axiom",
    Assume = "Assume",
    Subst = "Subst",
    Add = "Add",
    Bind = "Bind",
    VarElim = "VarElim",
    Infer = "Infer"
}

export enum AxiomSource {
    Axiom = "Axiom",
    Definition = "Definition",
    Sorry = "Sorry"
}

export type Proof<Id, Term> =
    | PAxiom<Id, Term>
    | PAssume<Term>
    | PSubst<Id, Term>
    | PAdd<Id, Term>
    | PBind<Id, Term>
    | PVarElim<Id, Term>
    | PInfer<Id, Term>

export type PAxiom<Id, Term> = {
    kind : ProofKind.Axiom
    rule : Rule<Term>,
    label : Id,
    source : AxiomSource
}

export type PAssume<Term> = {
    kind : ProofKind.Assume,
    rule : Rule<Term>,
    term : Term
}

export type PSubst<Id, Term> = {
    kind : ProofKind.Subst,
    rule : Rule<Term>,
    subst : Subst<Id, Term>,
    proof : Proof<Id, Term>
}

export type PAdd<Id, Term> = {
    kind : ProofKind.Add,
    rule : Rule<Term>,
    term : Term,
    proof : Proof<Id, Term>
}

export type PBind<Id, Term> = {
    kind : ProofKind.Bind,
    rule : Rule<Term>,
    term : Term,
    binders : Binder<Id>[],
    proof : Proof<Id, Term>
}

export type PVarElim<Id, Term> = {
    kind : ProofKind.VarElim,
    rule : Rule<Term>,
    id : Id,
    proof : Proof<Id, Term>
};

export type PInfer<Id, Term> = {
    kind : ProofKind.Infer,
    rule : Rule<Term>,
    template : Term,
    general : Proof<Id, Term>,
    instance : Proof<Id, Term>
}

export function ruleOfProof<Id, Term>(proof : Proof<Id, Term>) : Rule<Term> {
    return proof.rule;
}

export function removeDuplicatesInTermList<Id, Term>(terms : Terms<Id, Term>, termlist : Term[]) : Term[] {
    const collected = new HashSet(terms);
    const result : Term[] = [];
    for (const t of termlist) {
        if (collected.insert(t) === undefined) result.push(t);
    }
    return result;
}

export function removeDuplicatesInRule<Id, Term>(terms : Terms<Id, Term>, rule : Rule<Term>) :
    Rule<Term>
{
    return {
        premises : removeDuplicatesInTermList(terms, rule.premises),
        conclusion : rule.conclusion
    }
}

export function equalRules<Id, Term>(terms : Terms<Id, Term>,
    rule1 : Rule<Term>, rule2 : Rule<Term>) : boolean
{
    return arrayEqual(terms, rule1.premises, rule2.premises) &&
        terms.equal(rule1.conclusion, rule2.conclusion);
}
