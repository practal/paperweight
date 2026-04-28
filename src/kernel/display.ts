import { assertNever, Relation } from "things";
import { TermKind, BaseTerms } from "./terms.js";

export function displayTerm<Id, Term>(terms : BaseTerms<Id, Term>, term : Term, 
    needsBrackets : boolean = false) : string 
{
    const names : Id[] = [];
    const ids = terms.ids;
    function display(term : Term, needsBrackets : boolean) : string {
        const kind = terms.termKindOf(term);
        switch(kind) {
            case TermKind.bound: {
                const index = terms.destBoundVar(term);
                if (index >= 0 && index < names.length) {
                    const id = names[names.length - index - 1];
                    for (let i = 0; i < index; i++) {
                        if (ids.equal(id, names[names.length - i - 1])) {
                            return "↑" + index;
                        }
                    }
                    return ids.display(id);
                } else 
                    return "↑" + index;
            }
            case TermKind.template: {
                const [binders, body] = terms.destTemplate(term);
                names.push(...binders.toReversed());
                let result = binders.join(" ") + ". " + display(body, false);
                if (needsBrackets) result = "(" + result + ")";
                for (const _ of binders) names.pop();
                return result;
            }
            case TermKind.varapp: {
                const [varname, args] = terms.destVarApp(term);
                const name = ids.display(varname);
                if (args.length === 0) {
                    if (names.findIndex(id => terms.ids.compare(id, varname) === Relation.EQUAL) >= 0) 
                        return name + "[]";
                    else
                        return name;
                } else 
                    return name + "[" + args.map(t => display(t, false)).join(", ") + "]";
            }
            case TermKind.absapp: {
                let result = "";
                let brackets = false;
                const nameAndArgs = terms.destAbsApp(term);
                for (let i = 0; i < nameAndArgs.length; i++) {
                    const [varname, args] = nameAndArgs[i];
                    const name = ids.display(varname);
                    if (i > 0) {
                        brackets = true;
                        result += " ";
                        result += name;
                        result += ":";
                    } else {
                        result = name;
                    }
                    for (const arg of args) {
                        brackets = true;
                        result += " ";
                        result += display(arg, true);
                    }
                }
                if (needsBrackets && brackets) return "(" + result + ")";
                else return result;
            }   
            default: assertNever(kind);
        }
    }
    const result = display(term, needsBrackets);
    return result;
}

