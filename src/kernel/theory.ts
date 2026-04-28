import { force, freeze, HashMap, nat, RedBlackMap } from "things";
import { AbsSig, AbsSigSpec, emptySignature, equalAbsSig, Signature, specOfAbsSig } from "./signature.js";
import { Terms } from "./terms.js";
import { absSigOfAbsApp, validateRule, validateTerm } from "./validate.js";
import { removeDuplicatesInRule, Proof, ProofKind, equalRules, 
    PAssume, PAdd, PBind, removeDuplicatesInTermList, PVarElim,
    PInfer,
    PAxiom,
    AxiomSource} from "./proof.js";
import { isFreeWithArityZero, isNormalHead } from "./term-utils.js";
import { displayFreeVar, freeVarsOf, listFreeVars, subtractFreeVars } from "./free-vars.js";
import { applyRegularSubst, simpleSubstNoDangling, Subst, substVars, validateSubst } from "./subst.js";

export type Rule<Term> = { premises : Term[], conclusion : Term }

// Obviously not safe, but will do (for now).
export type Theorem<Id, Term> = { theory : Theory<Id, Term>, proof : Proof<Id, Term> }

export type Binder<Id> = BindIndex | BindVar<Id>

export type BindIndex = {
    index : nat
}

export type BindVar<Id> = {
    var : Id
}

export function isBindIndex<Id>(binder : Binder<Id>) : binder is BindIndex {
    return typeof ((binder as BindIndex)?.index) === "number";
}

export interface Theory<Id, Term> {

    terms : Terms<Id, Term>

    sig : Signature<Id>

    declare(absSigSpec : AbsSigSpec<Id>) : Theory<Id, Term>

    axiom(label : Id, rule : Rule<Term>) : Theory<Id, Term>

    defineWith(label : Id, relation : Term, head : Term, definiens : Term) : Theory<Id, Term>

    define(label : Id, head : Term, definiens : Term) : Theory<Id, Term>

    note(label : Id, thm : Theorem<Id, Term>) : Theory<Id, Term>

    theorem(label : Id) : Theorem<Id, Term>

    isAxiom(label : Id) : boolean

    isDefinition(label : Id) : boolean

    hasTheorem(label : Id) : boolean

    listAxioms() : Id[]

    listDefinitions() : Id[]

    listTheorems() : Id[]

    importTheory(thy : Theory<Id, Term>, allowAxioms : boolean) : Theory<Id, Term>

    /**
     * Proof rules
     */

    assume(term : Term) : Theorem<Id, Term>

    subst(substitution : Subst<Id, Term>, theorem : Theorem<Id, Term>) : Theorem<Id, Term>

    add(term : Term, theorem : Theorem<Id, Term>) : Theorem<Id, Term>

    bind(term : Term, binders : Binder<Id>[], theorem : Theorem<Id, Term>) : Theorem<Id, Term>

    varElim(id : Id, theorem : Theorem<Id, Term>) : Theorem<Id, Term>

    infer(template : Term, general : Theorem<Id, Term>, instance : Theorem<Id, Term>) : Theorem<Id, Term>

}

type Axioms<Id, Term> = RedBlackMap<Id, Rule<Term>>
type Definition<Term> = {
    relation : Term,
    head : Term,
    definiens : Term,
    rule : Rule<Term>
}
type Definitions<Id, Term> = RedBlackMap<Id, Definition<Term>>
type Theorems<Id, Term> = RedBlackMap<Id, Proof<Id, Term>>

function mkEquals<Id, Term>(terms : Terms<Id, Term>, lhs : Term, rhs : Term) : Term {
    const eq = terms.mkId("equals");
    return terms.mkAbsApp([[eq, [lhs, rhs]]])
}

function mkEqualsRelation<Id, Term>(terms : Terms<Id, Term>) : Term {
    const x = terms.mkId("x");
    const y = terms.mkId("y");
    return terms.mkTemplate([x, y], mkEquals(terms, terms.mkBoundVar(0), terms.mkBoundVar(1)));
}

function instantiateTemplate<Id, Term>(terms : Terms<Id, Term>, template : Term, args : Term[]) : Term {
    const [binders, body] = terms.destTemplate(template);
    if (binders.length !== args.length)
        throw new Error("Wrong number of arguments for template instantiation.");
    return simpleSubstNoDangling(terms, 0, body, args);
}

function mkDefinitionRule<Id, Term>(terms : Terms<Id, Term>, relation : Term,
    head : Term, definiens : Term) : Rule<Term>
{
    return {
        premises : [],
        conclusion : instantiateTemplate(terms, relation, [head, definiens])
    };
}

function equalDefinitions<Id, Term>(terms : Terms<Id, Term>,
    d1 : Definition<Term>, d2 : Definition<Term>) : boolean
{
    return terms.equal(d1.relation, d2.relation) &&
        terms.equal(d1.head, d2.head) &&
        terms.equal(d1.definiens, d2.definiens) &&
        equalRules(terms, d1.rule, d2.rule);
}

class Thy<Id, Term> implements Theory<Id, Term> {

    terms : Terms<Id, Term>
    sig : Signature<Id>
    #axioms : Axioms<Id, Term>
    #definitions : Definitions<Id, Term>
    #theorems : Theorems<Id, Term>

    constructor(terms : Terms<Id, Term>, sig : Signature<Id>, axioms : Axioms<Id, Term>,
        definitions : Definitions<Id, Term>, theorems : Theorems<Id, Term>)
    {
        this.terms = terms;
        this.sig = sig;
        this.#axioms = axioms;
        this.#definitions = definitions;
        this.#theorems = theorems;
        freeze(this);
    }

    listAxioms() : Id[] {
        return [...this.#axioms].map(r => r[0]);
    }

    listDefinitions() : Id[] {
        return [...this.#definitions].map(r => r[0]);
    }

    listTheorems() : Id[] {
        return [...this.#theorems].map(r => r[0]);
    }

    #axiom(label : Id) : Theorem<Id, Term> {
        const s = this.#axioms.get(label);
        if (s === undefined) throw new Error("No such axiom: " + this.terms.ids.display(label));
        const proof : PAxiom<Id, Term> = { kind : ProofKind.Axiom, label: label, rule : s, source : AxiomSource.Axiom };
        return { theory : this, proof : proof };
    }

    #definition(label : Id) : Theorem<Id, Term> {
        const d = this.#definitions.get(label);
        if (d === undefined) throw new Error("No such definition: " + this.terms.ids.display(label));
        const proof : PAxiom<Id, Term> = { kind : ProofKind.Axiom, label : label, rule : d.rule, source : AxiomSource.Definition };
        return { theory : this, proof : proof };
    }

    theorem(label : Id) : Theorem<Id, Term> {
        let proof = this.#theorems.get(label);
        if (proof !== undefined) return { theory : this, proof: proof };
        if (this.isAxiom(label)) return this.#axiom(label);
        if (this.isDefinition(label)) return this.#definition(label);
        throw new Error("No such theorem: " + this.terms.ids.display(label));
    }

    isAxiom(label : Id) : boolean {
        return this.#axioms.has(label);
    }

    hasTheorem(label : Id) : boolean {
        return this.isAxiom(label) || this.isDefinition(label) || this.#theorems.has(label);
    }

    isDefinition(label: Id): boolean {
        return this.#definitions.has(label);
    }

    declare(absSigSpec : AbsSigSpec<Id>) : Theory<Id, Term> {
        const newSig = this.sig.declare(absSigSpec);
        return new Thy(this.terms, newSig, this.#axioms, this.#definitions, this.#theorems);
    }

    axiom(label : Id, rule : Rule<Term>) : Theory<Id, Term> {
        this.#validateRule(rule);
        if (this.hasTheorem(label))
            throw new Error("There is already a theorem named '" + label + "', cannot introduce axiom.");
        const newAxioms = this.#axioms.set(label, removeDuplicatesInRule(this.terms, rule));
        return new Thy(this.terms, this.sig, newAxioms, this.#definitions, this.#theorems);
    }

    #findReflexiveTheoremLabel(relation : Term) : Id | undefined {
        const freeLabels = [...this.listAxioms(), ...this.listDefinitions(), ...this.listTheorems()];
        for (const label of freeLabels) {
            const theorem = this.theorem(label);
            if (theorem.proof.rule.premises.length !== 0) continue;
            const conclusion = theorem.proof.rule.conclusion;
            const freeVars = freeVarsOf(this.terms, conclusion);
            let witnessVar : Id | undefined = undefined;
            let candidate = true;
            for (const [id, arities] of freeVars) {
                for (const arity of arities) {
                    if (arity !== 0) {
                        candidate = false;
                        break;
                    }
                    if (witnessVar === undefined) witnessVar = id;
                    else if (!this.terms.ids.equal(witnessVar, id)) {
                        candidate = false;
                        break;
                    }
                }
                if (!candidate) break;
            }
            if (!candidate) continue;
            const z = witnessVar ?? this.terms.mkId("_");
            const reflexive = instantiateTemplate(this.terms, relation,
                [this.terms.mkVarApp(z, []), this.terms.mkVarApp(z, [])]);
            if (this.terms.equal(conclusion, reflexive)) return label;
        }
        return undefined;
    }

    defineWith(label : Id, relation : Term, head : Term, definiens : Term) : Theory<Id, Term> {
        if (this.hasTheorem(label))
            throw new Error("There is already a theorem named '" +
                this.terms.ids.display(label) + "', cannot introduce definition.");
        if (!isNormalHead(this.terms, head))
            throw new Error("Left hand side of definition is not a head: '" +
                this.terms.display(head) + "'.");
        if (this.terms.arityOfTemplate(relation) !== 2)
            throw new Error("Relation of definition must be a binary template.");
        this.#validate(relation);
        const freeVarsR = freeVarsOf(this.terms, relation);
        if (freeVarsR.size > 0) {
            const dangling = listFreeVars(freeVarsR).
                map(fv => displayFreeVar(this.terms.ids, fv)).join(", ");
            throw new Error("Free variables in relation of definition: " + dangling);
        }
        if (this.terms.arityOfTemplate(definiens) !== 0)
            throw new Error("Right hand side of definition must be a term.");
        this.#validate(definiens);
        const absSig = absSigOfAbsApp(this.terms, this.terms.destAbsApp(head));
        const newSig = this.sig.declare(specOfAbsSig(absSig));
        validateTerm(newSig, this.terms, head);
        const freeVarsH = freeVarsOf(this.terms, head);
        const freeVarsD = freeVarsOf(this.terms, definiens);
        subtractFreeVars(freeVarsD, freeVarsH);
        if (freeVarsD.size > 0) {
            const dangling = listFreeVars(freeVarsD).
                map(fv => displayFreeVar(this.terms.ids, fv)).join(", ");
            throw new Error("Dangling free variables in definiens: " + dangling);
        }
        const reflLabel = this.#findReflexiveTheoremLabel(relation);
        if (reflLabel === undefined)
            throw new Error("Could not find theorem witnessing reflexivity of relation.");
        const rule = mkDefinitionRule(this.terms, relation, head, definiens);
        validateRule(newSig, this.terms, rule);
        const newDefs = this.#definitions.set(label, {
            relation: relation,
            head: head,
            definiens: definiens,
            rule: rule
        });
        return new Thy(this.terms, newSig, this.#axioms, newDefs, this.#theorems);
    }

    define(label : Id, head : Term, definiens : Term) : Theory<Id, Term> {
        return this.defineWith(label, mkEqualsRelation(this.terms), head, definiens);
    }

    findDefinition(absSig : AbsSig<Id>) : Id | undefined {
        for (const [id, d] of this.#definitions) {
            const absSig2 = absSigOfAbsApp(this.terms, this.terms.destAbsApp(d.head));
            if (equalAbsSig(this.terms.ids, absSig, absSig2)) return id;
        }
        return undefined;
    }

    #declareViaImport(absSigSpec : AbsSigSpec<Id>) : Thy<Id, Term> {
        if (!this.sig.specIsDeclared(absSigSpec)) {
            return this.declare(absSigSpec) as Thy<Id, Term>;
        } else return this;
    }

    #axiomViaImport(label : Id, axiom : Rule<Term>) : Thy<Id, Term> {
        if (this.hasTheorem(label)) {
            const currentAxiom = this.theorem(label);
            if (!equalRules(this.terms, currentAxiom.proof.rule, axiom))
                throw new Error("Cannot import theory, imported axiom '" +
                    this.terms.ids.display(label) + "' differs from present theorem.");
            return this;
        } else {
            return this.axiom(label, axiom) as Thy<Id, Term>;
        }
    }

    #noteViaImport(label : Id, proof : Proof<Id, Term>) : Thy<Id, Term> {
        if (this.hasTheorem(label)) {
            const currentThm = this.theorem(label);
            if (!equalRules(this.terms, currentThm.proof.rule, proof.rule))
                throw new Error("Cannot import theory, imported theorem '" +
                    this.terms.ids.display(label) + "' differs from present theorem.");
            return this;
        } else {
            const newTheorems = this.#theorems.set(label, proof);
            return new Thy(this.terms, this.sig, this.#axioms, this.#definitions, newTheorems);
        }
    }

    #defineViaImport(label : Id, d : Definition<Term>, rule : Rule<Term>) : Thy<Id, Term> {
        if (this.hasTheorem(label)) {
            if (this.isDefinition(label)) {
                const currentD = force(this.#definitions.get(label));
                if (!equalDefinitions(this.terms, currentD, d))
                    throw new Error("Cannot import theory, imported definition '" +
                        this.terms.ids.display(label) + "' differs from present definition.");
                return this;
            } else {
                const currentThm = this.theorem(label);
                if (!equalRules(this.terms, currentThm.proof.rule, rule))
                    throw new Error("Cannot import theory, imported definition '" +
                        this.terms.ids.display(label) + "' differs from present theorem.");
                return this;
            }
        }
        const absSig = absSigOfAbsApp(this.terms, this.terms.destAbsApp(d.head));
        const previousDefLabel = this.findDefinition(absSig);
        if (previousDefLabel !== undefined) {
            const previousD = force(this.#definitions.get(previousDefLabel));
            if (!equalDefinitions(this.terms, d, previousD))
                throw new Error("Cannot import theory, imported definition '" +
                    this.terms.ids.display(label) + "' clashes with definition '"+
                    this.terms.ids.display(previousDefLabel) + "'.");
        }
        const newDefs = this.#definitions.set(label, d);
        return new Thy(this.terms, this.sig, this.#axioms, newDefs, this.#theorems);
    }


    #checkTheory(theorem : Theorem<Id, Term>) {
        if (theorem.theory !== this) throw new Error("Theorem is not compatible with this theory.");
    }

    note(label : Id, thm : Theorem<Id, Term>) : Theory<Id, Term> {
        this.#checkTheory(thm);
        if (this.hasTheorem(label))
            throw new Error("There is already a theorem named '" +
                this.terms.ids.display(label) + "'.");
        const newTheorems = this.#theorems.set(label, thm.proof);
        return new Thy(this.terms, this.sig, this.#axioms, this.#definitions, newTheorems);
    }

    importTheory(_thy : Theory<Id, Term>, allowAxioms : boolean) : Theory<Id, Term> {
        let currentTheory : Thy<Id, Term> = this;
        const thy = _thy as Thy<Id, Term>;
        for (const [_, absSigSpecs] of thy.sig.allAbsSigSpecs()) {
            for (const absSigSpec of absSigSpecs) {
                currentTheory = currentTheory.#declareViaImport(absSigSpec);
            }
        }
        for (const label of thy.listAxioms()) {
            const axiom = thy.theorem(label).proof.rule;
            currentTheory = currentTheory.#axiomViaImport(label, axiom);
            if (!allowAxioms && currentTheory.#axioms.size > this.#axioms.size) {
                throw new Error("importTheory: no new axioms allowed in import.");
            }
        }
        for (const label of thy.listDefinitions()) {
            const d = force(thy.#definitions.get(label));
            const rule = thy.theorem(label).proof.rule;
            currentTheory = currentTheory.#defineViaImport(label, d, rule);
        }
        for (const [label, proof] of thy.#theorems) {
            currentTheory = currentTheory.#noteViaImport(label, proof);
        }
        return currentTheory;
    }

    #validate(term : Term) {
        validateTerm(this.sig, this.terms, term);
    }

    #validateRule(rule : Rule<Term>) {
        validateRule(this.sig, this.terms, rule);
    }

    assume(term : Term) : Theorem<Id, Term> {
        this.#validate(term);
        const proof : PAssume<Term> = {
            kind : ProofKind.Assume,
            rule : { premises : [term], conclusion : term },
            term : term
        };
        return { theory : this, proof : proof };
    }

    subst(substitution : Subst<Id, Term>, theorem : Theorem<Id, Term>) : Theorem<Id, Term> {
        this.#checkTheory(theorem);
        validateSubst(this.sig, this.terms, substitution);
        const rule : Rule<Term> = {
            premises: theorem.proof.rule.premises.map(t =>
                applyRegularSubst(this.terms, t, substitution)),
            conclusion: applyRegularSubst(this.terms, theorem.proof.rule.conclusion, substitution)
        };
        const proof : Proof<Id, Term> = {
            kind: ProofKind.Subst,
            rule : removeDuplicatesInRule(this.terms, rule),
            subst: substitution,
            proof: theorem.proof
        }
        return { theory : this, proof : proof };
    }

    add(term : Term, theorem : Theorem<Id, Term>) : Theorem<Id, Term> {
        this.#checkTheory(theorem);
        this.#validate(term);
        const premises = [term, ...theorem.proof.rule.premises];
        const proof : PAdd<Id, Term> = {
            kind : ProofKind.Add,
            rule : removeDuplicatesInRule(this.terms, {
                premises: premises,
                conclusion : theorem.proof.rule.conclusion}),
            term : term,
            proof : theorem.proof
        };
        return { theory : this, proof : proof };
    }

    #changeBinders(term : Term, binders : Binder<Id>[]) : Term {
        const [termBinders, termBody] = this.terms.destTemplate(term);
        let boundVars : Map<nat, nat> = new Map();
        let freeVars : HashMap<Id, nat> = new HashMap(this.terms.ids);
        let newBinders : Id[] = [];
        for (let i = 0; i < binders.length; i++) {
            const binder = binders[i];
            if (isBindIndex(binder)) {
                if (boundVars.has(binder.index))
                    throw new Error("checkBinders: duplicate binder index " + binder.index);
                if (binder.index >= termBinders.length)
                    throw new Error("checkBinders: invalid binder index " + binder.index);
                newBinders.push(termBinders[binder.index]);
                boundVars.set(binder.index, i);
            } else {
                newBinders.push(binder.var);
                freeVars.putIfNew(binder.var, () => i);
            }
        }
        const result = this.terms.mkTemplate(newBinders,
            substVars(this.terms, boundVars, freeVars, termBody));
        this.#validate(result);
        return result;
    }

    #replaceTerm(termlist : Term[], term : Term, replacement : Term) : Term[] | undefined {
        for (let i = 0; i < termlist.length; i++) {
            if (this.terms.equal(termlist[i], term)) {
                const replaced = [...termlist];
                replaced[i] = replacement;
                return removeDuplicatesInTermList(this.terms, replaced);
            }
        }
        return undefined;
    }

    bind(term : Term, binders : Binder<Id>[], theorem : Theorem<Id, Term>) : Theorem<Id, Term>
    {
        this.#checkTheory(theorem);
        const changed = this.#changeBinders(term, binders);
        const premises = this.#replaceTerm(theorem.proof.rule.premises, term, changed);
        if (premises === undefined) throw new Error("bind: no such term found.");
        const rule : Rule<Term> = {
            premises : premises,
            conclusion : theorem.proof.rule.conclusion
        };
        const proof : PBind<Id, Term> = {
            kind : ProofKind.Bind,
            rule : rule,
            term : term,
            binders : binders,
            proof : theorem.proof
        };
        return { theory : this, proof : proof };
    }

    #removeStrictly(ids : Id[], term : Term, termlist : Term[]) : Term[] | undefined {
        const result : Term[] = [];
        for (const t of termlist) {
            if (!this.terms.equal(term, t)) {
                if (isFreeWithArityZero(this.terms, ids, t)) return undefined;
                result.push(t);
            }
        }
        if (result.length === termlist.length) return undefined;
        return result;
    }

    #removeFree(id : Id, termlist : Term[]) : Term[] | undefined {
        const v = this.terms.mkVarApp(id, []);
        return this.#removeStrictly([id], v, termlist);
    }

    // Returns if any of the identifiers occurs free with arity zero in any of the terms
    #isFreeWithArityZero(ids : Id[], termlist : Term[]) : boolean {
        for (const t of termlist) {
            if (isFreeWithArityZero(this.terms, ids, t)) return true;
        }
        return false;
    }

    varElim(id : Id, theorem : Theorem<Id, Term>) : Theorem<Id, Term> {
        this.#checkTheory(theorem);
        const premises = this.#removeFree(id, theorem.proof.rule.premises);
        if (premises === undefined ||
            isFreeWithArityZero(this.terms, [id], theorem.proof.rule.conclusion))
            throw new Error("varElim: variable '" + this.terms.ids.display(id) +
                "' cannot be discarded.");
        const rule = {
            premises: premises,
            conclusion : theorem.proof.rule.conclusion
        };
        const proof : PVarElim<Id, Term> = {
            kind : ProofKind.VarElim,
            rule : rule,
            id : id,
            proof : theorem.proof
        };
        return { theory : this, proof : proof };
    }

    #instanceOf(template : Term) : [Term, Id[]] {
        const [binders, body] = this.terms.destTemplate(template);
        const args = binders.map(b => this.terms.mkVarApp(b, []));
        return [simpleSubstNoDangling(this.terms, 0, body, args), binders];
    }

    infer(template: Term, general: Theorem<Id, Term>, instance: Theorem<Id, Term>): Theorem<Id, Term> {
        this.#checkTheory(general);
        this.#checkTheory(instance);
        const [term, binders] = this.#instanceOf(template);
        const modifiedPremises = this.#removeStrictly([], template, general.proof.rule.premises);
        if (modifiedPremises === undefined) throw new Error("infer: no such template found in premises");
        if (!this.terms.equal(instance.proof.rule.conclusion, term))
            throw new Error("infer: instance conclusion does not match template instantiation");
        if (this.#isFreeWithArityZero(binders, instance.proof.rule.premises))
            throw new Error("infer: bound variables of template occur free in instance premises");
        const rule : Rule<Term> = removeDuplicatesInRule(this.terms, {
            premises: [...modifiedPremises, ...instance.proof.rule.premises],
            conclusion: general.proof.rule.conclusion
        });
        const proof : PInfer<Id, Term> = {
            kind: ProofKind.Infer,
            rule: rule,
            template: template,
            general: general.proof,
            instance: instance.proof
        }
        return { theory : this, proof : proof }
    }

}
freeze(Thy);

export function emptyTheory<Id, Term>(terms : Terms<Id, Term>) : Theory<Id, Term> {
    return new Thy(terms, emptySignature(terms.ids), RedBlackMap(terms.ids),
        RedBlackMap(terms.ids),  RedBlackMap(terms.ids));
}
