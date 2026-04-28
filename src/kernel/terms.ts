import { assertTrue, Data, freeze, int, nat, Relation } from "things"
import { hashTerm } from "./hash.js";
import { compareTerms } from "./compare.js";
import { displayTerm } from "./display.js";

export enum TermKind {
    varapp = "varapp",
    absapp = "absapp",
    bound = "bound",
    template = "template"
}

export function isTermKind(kind : any) : kind is TermKind {
    return kind === TermKind.absapp || kind === TermKind.varapp 
        || kind === TermKind.bound || kind === TermKind.template;
}

export interface BaseTerms<Id, Term> {
    
    ids : Data<Id>
            
    mkId(id : string) : Id
    
    termKindOf(term : Term) : TermKind
    
    destVarApp(term : Term) : [Id, Term[]]
    
    destAbsApp(term : Term) : [Id, Term[]][]
    
    destBoundVar(term : Term) : nat
    
    destTemplate(term : Term) : [Id[], Term]
    
    arityOfTemplate(term : Term) : nat

    mkVarApp(varname : Id, args : Term[]) : Term
    
    mkAbsApp(absapp : [Id, Term[]][]) : Term
    
    mkBoundVar(index : nat) : Term
    
    mkTemplate(binders : Id[], body : Term) : Term

}

export interface Terms<Id, Term> extends BaseTerms<Id, Term>, Data<Term>{}

export function termsFromBase<Id, Term>(base : BaseTerms<Id, Term>, 
    name : string, isTerm : (_ : any) => boolean) : Terms<Id, Term> 
{
    return new TermsFromBase(base, name, isTerm);
}

class TermsFromBase<Id, Term> implements Terms<Id, Term> {
    
    #base : BaseTerms<Id, Term>
    #isTerm : (_ : any) => boolean
    
    ids: Data<Id>;
    
    name : string;
    
    constructor(base : BaseTerms<Id, Term>, name : string, isTerm : (_ : any) => boolean) {
        this.#base = base;
        this.ids = base.ids;
        this.name = name;
        this.#isTerm = isTerm;
        freeze(this);
    }
    
    mkId(id: string): Id {
        return this.#base.mkId(id);
    }
    
    termKindOf(term: Term): TermKind {
        return this.#base.termKindOf(term);
    }

    destVarApp(term: Term): [Id, Term[]] {
        return this.#base.destVarApp(term);
    }
    
    destAbsApp(term: Term): [Id, Term[]][] {
        return this.#base.destAbsApp(term);
    }
    
    destBoundVar(term: Term): nat {
        return this.#base.destBoundVar(term);
    }
    
    destTemplate(term: Term): [Id[], Term] {
        return this.#base.destTemplate(term);
    }
    
    arityOfTemplate(term: Term): nat {
        return this.#base.arityOfTemplate(term);
    }
    
    mkVarApp(varname: Id, args: Term[]): Term {
        return this.#base.mkVarApp(varname, args);
    }
    
    mkAbsApp(absapp: [Id, Term[]][]): Term {
        return this.#base.mkAbsApp(absapp);
    }
    
    mkBoundVar(index: nat): Term {
        return this.#base.mkBoundVar(index);
    }
    
    mkTemplate(binders: Id[], body: Term): Term {
        return this.#base.mkTemplate(binders, body);
    }
    
    hash(term: Term): int {
        return hashTerm(this.#base, term);
    }
    
    equal(x: Term, y: Term): boolean {
        return compareTerms(this.#base, x, y) === Relation.EQUAL;
    }
    
    is(value: any): value is Term {
        return this.#isTerm(value);
    }
    
    assert(value: any): asserts value is Term {
        assertTrue(this.#isTerm(value), "Term assertion failed.");
    }
    
    display(term: Term): string {
        return displayTerm(this.#base, term);
    }
    
    compare(x: Term, y: Term): Relation {
        return compareTerms(this.#base, x, y);
    }
    
}
freeze(TermsFromBase);

