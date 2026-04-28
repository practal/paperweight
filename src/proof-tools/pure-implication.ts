import { Thm, parse, subst, S, thm } from "../workbench.js";
import { modusPonens, impliesRefl } from "../theories/Implication.theory.js";

export type ProofTy =
    | { kind: "atom"; name: string }
    | { kind: "imp"; left: ProofTy; right: ProofTy }
    | { kind: "tvar"; id: number };

export type ProofExpr =
    | { kind: "var"; name: string }
    | { kind: "app"; fn: ProofExpr; arg: ProofExpr; inferred?: ProofTy }
    | { kind: "lam"; name: string; ty: ProofTy; body: ProofExpr }
    | { kind: "S"; inferred?: ProofTy }
    | { kind: "K"; inferred?: ProofTy }
    | { kind: "I"; inferred?: ProofTy };

export function tyAtom(name: string): ProofTy {
    return { kind: "atom", name };
}

export function tyImp(left: ProofTy, right: ProofTy): ProofTy {
    return { kind: "imp", left, right };
}

export function v(name: string): ProofExpr {
    return { kind: "var", name };
}

export function app(fn: ProofExpr, arg: ProofExpr): ProofExpr {
    return { kind: "app", fn, arg };
}

export function lam(name: string, ty: ProofTy, body: ProofExpr): ProofExpr {
    return { kind: "lam", name, ty, body };
}

// Typed SKI synthesis for closed implication-only tautologies.
export function provePureImplication(goal: ProofTy, expr: ProofExpr): Thm {
    let nextTvar = 0;
    const substitution = new Map<number, ProofTy>();
    const freshTvar = (): ProofTy => ({ kind: "tvar", id: ++nextTvar });

    function applyTySubst(ty: ProofTy): ProofTy {
        if (ty.kind === "tvar" && substitution.has(ty.id))
            return applyTySubst(substitution.get(ty.id)!);
        if (ty.kind === "imp")
            return tyImp(applyTySubst(ty.left), applyTySubst(ty.right));
        return ty;
    }

    function occurs(id: number, ty: ProofTy): boolean {
        const normalized = applyTySubst(ty);
        if (normalized.kind === "tvar") return normalized.id === id;
        if (normalized.kind === "imp") return occurs(id, normalized.left) || occurs(id, normalized.right);
        return false;
    }

    function unify(left: ProofTy, right: ProofTy): void {
        const normalizedLeft = applyTySubst(left);
        const normalizedRight = applyTySubst(right);
        if (normalizedLeft.kind === "tvar") {
            if (normalizedRight.kind === "tvar" && normalizedLeft.id === normalizedRight.id) return;
            if (occurs(normalizedLeft.id, normalizedRight))
                throw new Error("provePureImplication: occurs check failed.");
            substitution.set(normalizedLeft.id, normalizedRight);
            return;
        }
        if (normalizedRight.kind === "tvar") {
            unify(normalizedRight, normalizedLeft);
            return;
        }
        if (normalizedLeft.kind === "atom" && normalizedRight.kind === "atom") {
            if (normalizedLeft.name !== normalizedRight.name)
                throw new Error("provePureImplication: atom mismatch.");
            return;
        }
        if (normalizedLeft.kind === "imp" && normalizedRight.kind === "imp") {
            unify(normalizedLeft.left, normalizedRight.left);
            unify(normalizedLeft.right, normalizedRight.right);
            return;
        }
        throw new Error("provePureImplication: cannot unify implication types.");
    }

    function freeVars(term: ProofExpr): Set<string> {
        switch (term.kind) {
            case "var":
                return new Set([term.name]);
            case "app": {
                const result = freeVars(term.fn);
                for (const name of freeVars(term.arg)) result.add(name);
                return result;
            }
            case "lam": {
                const result = freeVars(term.body);
                result.delete(term.name);
                return result;
            }
            default:
                return new Set();
        }
    }

    function abstractVar(name: string, term: ProofExpr): ProofExpr {
        if (!freeVars(term).has(name)) return app({ kind: "K" }, term);
        if (term.kind === "var" && term.name === name) return { kind: "I" };
        if (term.kind === "app")
            return app(app({ kind: "S" }, abstractVar(name, term.fn)), abstractVar(name, term.arg));
        throw new Error("provePureImplication: unsupported abstraction shape.");
    }

    function toSki(term: ProofExpr): ProofExpr {
        switch (term.kind) {
            case "var":
                return term;
            case "app":
                return app(toSki(term.fn), toSki(term.arg));
            case "lam":
                return toSki(abstractVar(term.name, toSki(term.body)));
            default:
                return term;
        }
    }

    function inferType(term: ProofExpr): ProofTy {
        switch (term.kind) {
            case "var":
                throw new Error("provePureImplication: open SKI term.");
            case "S": {
                const A = freshTvar();
                const B = freshTvar();
                const C = freshTvar();
                term.inferred = tyImp(tyImp(A, tyImp(B, C)), tyImp(tyImp(A, B), tyImp(A, C)));
                return term.inferred;
            }
            case "K": {
                const A = freshTvar();
                const B = freshTvar();
                term.inferred = tyImp(A, tyImp(B, A));
                return term.inferred;
            }
            case "I": {
                const A = freshTvar();
                term.inferred = tyImp(A, A);
                return term.inferred;
            }
            case "app": {
                const fnType = inferType(term.fn);
                const argType = inferType(term.arg);
                const resultType = freshTvar();
                unify(fnType, tyImp(argType, resultType));
                term.inferred = applyTySubst(resultType);
                return term.inferred;
            }
            case "lam":
                throw new Error("provePureImplication: expected a closed lambda term.");
        }
    }

    function normalizeInferred(term: ProofExpr): void {
        if (term.kind === "app") {
            normalizeInferred(term.fn);
            normalizeInferred(term.arg);
        }
        if ("inferred" in term && term.inferred !== undefined) term.inferred = applyTySubst(term.inferred);
    }

    function tyToFormula(ty: ProofTy): string {
        const normalized = applyTySubst(ty);
        if (normalized.kind === "atom") return normalized.name;
        if (normalized.kind === "tvar")
            throw new Error("provePureImplication: unresolved type variable.");
        const renderSide = (side: ProofTy): string => {
            const rendered = tyToFormula(side);
            return applyTySubst(side).kind === "atom" ? rendered : `(${rendered})`;
        };
        return `implies ${renderSide(normalized.left)} ${renderSide(normalized.right)}`;
    }

    function buildTheorem(term: ProofExpr): Thm {
        switch (term.kind) {
            case "S": {
                const inferred = term.inferred!;
                if (inferred.kind !== "imp" || inferred.left.kind !== "imp" || inferred.left.right.kind !== "imp")
                    throw new Error("provePureImplication: malformed S type.");
                return subst(
                    S(
                        "A", tyToFormula(inferred.left.left),
                        "B", tyToFormula(inferred.left.right.left),
                        "C", tyToFormula(inferred.left.right.right),
                    ),
                    thm("implies_2"),
                );
            }
            case "K": {
                const inferred = term.inferred!;
                if (inferred.kind !== "imp" || inferred.right.kind !== "imp")
                    throw new Error("provePureImplication: malformed K type.");
                return subst(
                    S("A", tyToFormula(inferred.left), "B", tyToFormula(inferred.right.left)),
                    thm("implies_1"),
                );
            }
            case "I": {
                const inferred = term.inferred!;
                if (inferred.kind !== "imp")
                    throw new Error("provePureImplication: malformed I type.");
                return impliesRefl(parse(tyToFormula(inferred.left))!);
            }
            case "app":
                return modusPonens(buildTheorem(term.fn), buildTheorem(term.arg));
            case "var":
            case "lam":
                throw new Error("provePureImplication: build expected a closed SKI term.");
        }
    }

    const ski = toSki(expr);
    const inferred = inferType(ski);
    unify(inferred, goal);
    normalizeInferred(ski);
    return buildTheorem(ski);
}
