import { addHash, assertNever, int, string } from "things";
import { TermKind, BaseTerms } from "./terms.js";

const termH = string.hash("Term");
const absAppH = string.hash("AbsApp");
const varAppH = string.hash("VarApp");
const templateH = string.hash("Template");
const boundH = string.hash("Bound");

export function hashTerm<Id, Term>(terms : BaseTerms<Id, Term>, term : Term) : int {
    let code : int = termH;
    function add(h : int) {
        code = addHash(code, h);
    }
    const ids = terms.ids;
    function hash(term : Term) {
        const kind = terms.termKindOf(term);
        switch (kind) {
            case TermKind.absapp: {
                add(absAppH);
                const nameAndArgs = terms.destAbsApp(term);
                for (const [name, args] of nameAndArgs) {
                    add(ids.hash(name));
                    for (const arg of args) hash(arg);
                }
                break;
            }
            case TermKind.varapp: {
                add(varAppH);
                const [name, args] = terms.destVarApp(term);
                add(ids.hash(name));
                for (const arg of args) hash(arg);
                break;
            }
            case TermKind.bound: {
                add(boundH);
                add(int.hash(terms.destBoundVar(term)));
                break;
            }
            case TermKind.template: {
                add(templateH);
                const [binders, body] = terms.destTemplate(term);
                add(int.hash(binders.length));
                hash(body);
                break;
            }
            default: assertNever(kind);
        }
    }
    hash(term);
    return code;
}
