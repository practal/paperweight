import { Data, freeze, nat, string } from "things";
import {BaseTerms, isTermKind, TermKind, Terms, termsFromBase} from "./terms.js";

export type Id = string
export type Term = VarApp | AbsApp | Bound | Template

type VarApp = {
    kind : TermKind.varapp,
    name : Id,
    args : Term[] // args can never be templates
}

type AbsApp = {
    kind : TermKind.absapp,
    nameAndArgs : [Id, Term[]][] // this is never empty
} 

type Bound = {
    kind : TermKind.bound,
    index : nat
}

type Template = {
    kind : TermKind.template,
    binders : Id[], // terms are normalized so that this is never empty
    body : Term // this will never be a template
}

function checkTerm(term : any) : term is Term {
    return isTermKind(term?.kind);
}

class DefaultTerms implements BaseTerms<Id, Term> {
    
    ids: Data<Id>;
    
    constructor() {
        this.ids = string;
        freeze(this);
    }
        
    mkId(id: string): Id {
        return id;
    }
    
    incrementId(id: Id): Id {
        return id + "'";
    }
    
    termKindOf(term: Term): TermKind {
        return term.kind;
    }
    
    destVarApp(term: Term): [Id, Term[]] {
        if (term.kind === TermKind.varapp) {
            return [term.name, term.args];
        }
        throw new Error("Wrong term kind '" + term.kind + "' for destVarApp");
    }
    
    destAbsApp(term: Term): [Id, Term[]][] {
        if (term.kind === TermKind.absapp) {
            return term.nameAndArgs;
        } 
        throw new Error("Wrong term kind '" + term.kind + "' for destAbsApp.");
    }
    
    destBoundVar(term: Term): nat {
        if (term.kind === TermKind.bound) {
            return term.index;
        } 
        throw new Error("Wrong term kind '" + term.kind + "' for destBoundVar.");
    }
    
    destTemplate(term: Term): [Id[], Term] {
        if (term.kind === TermKind.template) {
            return [term.binders, term.body];
        } else {
            // a term is a nullary template
            return [[], term];
        }
    }
    
    arityOfTemplate(term : Term) : nat {
        if (term.kind === TermKind.template) {
            return term.binders.length;
        } else {
            // a term is a nullary template
            return 0;
        }
    }
    
    mkVarApp(varname: Id, args: Term[]): Term {
        for (const arg of args) {
            if (arg.kind === TermKind.template) throw new Error("Variable cannot be applied to templates.");
        }
        return {
            kind: TermKind.varapp,
            name: varname,
            args: args
        };
    }
    
    mkAbsApp(absapp: [Id, Term[]][]): Term {
        if (absapp.length === 0) throw new Error("Abstraction application cannot be empty.");
        return {
            kind: TermKind.absapp,
            nameAndArgs: absapp
        };
    }
    
    mkBoundVar(index: nat): Term {
        return {
            kind: TermKind.bound,
            index: index
        };
    }
    
    mkTemplate(binders: string[], body: Term): Term {
        if (body.kind === TermKind.template) throw new Error("Body of template cannot be a template.");
        if (binders.length === 0) return body;
        return {
            kind: TermKind.template,
            binders: binders,
            body: body
        };
    }

}
freeze(DefaultTerms);

export const defaultTerms : Terms<Id, Term> = termsFromBase(
    new DefaultTerms(), "defaultTerms", checkTerm);
