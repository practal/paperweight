import { assertNever, Relation } from "things";
import { TermKind, BaseTerms } from "./terms.js";

export function displayTermAsTeX<Id, Term>(terms : BaseTerms<Id, Term>, term : Term, 
    needsBrackets : boolean = false, deBruijn : boolean = false) : string 
{
    const names : Id[] = [];
    const ids = terms.ids;
    function display(term : Term, needsBrackets : boolean) : string {
        const kind = terms.termKindOf(term);
        switch(kind) {
            case TermKind.bound: {
                const index = terms.destBoundVar(term);
                if (index < names.length && !deBruijn) {
                    const id = names[names.length - index - 1];
                    for (let i = 0; i < index; i++) {
                        if (ids.equal(id, names[names.length - i - 1])) {
                            return "\\dbi{" + index + "}";
                        }
                    }
                    return "\\bvar{" + ids.display(id) + "}";
                } else 
                    return "\\dbi{" + index + "}";
            }
            case TermKind.template: {
                const [binders, body] = terms.destTemplate(term);
                if (!deBruijn) {
                    names.push(...binders.toReversed());
                    let bounds = binders.map(b => "\\bvar{" + ids.display(b) + "}");
                    let result = bounds.join("\\,") + "\\p.\\," + display(body, false);
                    if (needsBrackets) result = "\\bround{" + result + "}";
                    for (const _ of binders) names.pop();
                    return result;
                } else {
                    let result = display(body, false);
                    if (needsBrackets) result = "\\bround{" + result + "}";
                    return result;
                }
            }
            case TermKind.varapp: {
                const [varname, args] = terms.destVarApp(term);
                const name = "\\var{" + ids.display(varname) + "}";
                if (args.length === 0) {
                    if (names.findIndex(id => terms.ids.compare(id, varname) === Relation.EQUAL) >= 0) 
                        return name + "\\bsquare{}";
                    else
                        return name;
                } else 
                    return name + "\\bsquare{" + args.map(t => display(t, false)).join("\\p,\\,") + "}";
            }
            case TermKind.absapp: {
                let result = "";
                let brackets = false;
                const nameAndArgs = terms.destAbsApp(term);
                for (let i = 0; i < nameAndArgs.length; i++) {
                    const [absname, args] = nameAndArgs[i];
                    const name = "\\abs{" + ids.display(absname) + "}";
                    if (i > 0) {
                        brackets = true;
                        result += "\\,";
                        result += name;
                        result += "\\p:";
                    } else {
                        result = name;
                    }
                    for (const arg of args) {
                        brackets = true;
                        result += "\\,";
                        result += display(arg, true);
                    }
                }
                if (needsBrackets && brackets) return "\\bround{" + result + "}";
                else return result;
            }   
            default: assertNever(kind);
        }
    }
    const result = display(term, needsBrackets);
    return result;
}

