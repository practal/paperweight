import { assertNever, int, Relation, string } from "things";
import { TermKind, BaseTerms } from "./terms.js";

export function compareTerms<Id, Term>(terms : BaseTerms<Id, Term>, term1 : Term, term2 : Term) : Relation {
    const ids = terms.ids;
    function compare(term1 : Term, term2 : Term) : Relation {
        const kind = terms.termKindOf(term1);
        let cmp = string.compare(kind, terms.termKindOf(term2));
        if (cmp !== Relation.EQUAL) return cmp;
        switch (kind) {
            case TermKind.absapp: {
                const nameAndArgs1 = terms.destAbsApp(term1);
                const nameAndArgs2 = terms.destAbsApp(term2);
                cmp = int.compare(nameAndArgs1.length, nameAndArgs2.length);
                if (cmp !== Relation.EQUAL) return cmp;
                for (let i = 0; i < nameAndArgs1.length; i++) {
                    const [name1, args1] = nameAndArgs1[i];
                    const [name2, args2] = nameAndArgs2[i];
                    cmp = ids.compare(name1, name2);
                    if (cmp !== Relation.EQUAL) return cmp;
                    cmp = int.compare(args1.length, args2.length);
                    if (cmp !== Relation.EQUAL) return cmp;
                    for (let j = 0; j < args1.length; j++) {
                        cmp = compare(args1[j], args2[j]);
                        if (cmp !== Relation.EQUAL) return cmp;
                    }
                }
                return Relation.EQUAL;
            }
            case TermKind.bound: {
                const index1 = terms.destBoundVar(term1);
                const index2 = terms.destBoundVar(term2);
                return int.compare(index1, index2);
            }
            case TermKind.varapp: {
                const [name1, args1] = terms.destVarApp(term1);
                const [name2, args2] = terms.destVarApp(term2);
                cmp = ids.compare(name1, name2);
                if (cmp !== Relation.EQUAL) return cmp;
                cmp = int.compare(args1.length, args2.length);
                for (let i = 0; i < args1.length; i++) {
                    cmp = compare(args1[i], args2[i]);
                    if (cmp !== Relation.EQUAL) return cmp;
                }
                return Relation.EQUAL;
            }
            case TermKind.template: {
                const [binders1, body1] = terms.destTemplate(term1);
                const [binders2, body2] = terms.destTemplate(term2);
                cmp = int.compare(binders1.length, binders2.length);
                if (cmp !== Relation.EQUAL) return cmp;
                return compare(body1, body2);
            }
            default: assertNever(kind);
        }
    }
    return compare(term1, term2);
}
