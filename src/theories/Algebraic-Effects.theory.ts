import { beginTheory, declare, axiom, endTheory, includeTheory, have, thm, subst, S, Thm } from "../workbench.js";
import { equalsTrans, equalsSym } from "./Equality.theory.js";

// ============================================================
// Algebraic Effects in Abstraction Logic
// ============================================================
//
// Algebraic effects model computational side-effects as
// operations with algebraic laws.
//
// References:
//   [1] G. Plotkin, J. Power, "Algebraic Operations and Generic Effects",
//       Applied Categorical Structures 11(1), pp. 69–94, 2003.
//       https://doi.org/10.1023/A:1023064908962
//
//   [2] G. Plotkin, M. Pretnar, "Handlers of Algebraic Effects",
//       ESOP 2009, pp. 80–94.
//       https://doi.org/10.1007/978-3-642-00590-9_7
//
//   [3] A. Bauer, "Programming with Effects I: Theory", 2010.
//       https://math.andrej.com/2010/09/27/programming-with-effects-i-theory/
//
// ============================================================
// Mutable State
// ============================================================
//
// A single mutable cell.
//
// In Bauer's framework [3]:
//   get : 1 × A^S → A   (arity S — continuation receives the state)
//   put : S × A^1 → A   (arity 1 — continuation receives nothing)

beginTheory();
includeTheory("Equality");

declare("get continue: (s. K[s])");
declare("put v continue: K");

// get-get: consecutive reads return the same value
axiom("get-get",
    "equals (get continue: (s. get continue: (t. K[s, t]))) (get continue: (s. K[s, s]))");

// get-put: storing what was just read is a no-op
axiom("get-put",
    "equals (get continue: (s. put s continue: K)) K");

// put-get: reading after storing returns the stored value
axiom("put-get",
    "equals (put v continue: (get continue: (s. K[s]))) (put v continue: K[v])");

// put-put: consecutive stores — last write wins
axiom("put-put",
    "equals (put u continue: (put v continue: K)) (put v continue: K)");

// ============================================================
// Exceptions
// ============================================================
//
// In Bauer's framework [3]:
//   raise : E × A^0 → A   (arity 0 — no continuation)

declare("raise e continue:");

// ============================================================
// Nondeterminism
// ============================================================
//
// In Bauer's framework [3]:
//   choose : 1 × A^2 → A   (arity 2 — two continuations)
//
// No parameters, two continuations: the operation
// nondeterministically selects one of the two branches.

declare("choose continue: K L");

// Idempotency: choosing between identical alternatives is no choice
axiom("choose_idem", "equals (choose continue: K K) K");

// Commutativity: the order of alternatives does not matter
axiom("choose_comm", "equals (choose continue: K L) (choose continue: L K)");

// Associativity: grouping of alternatives does not matter
axiom("choose_assoc",
    "equals (choose continue: (choose continue: K L) M) (choose continue: K (choose continue: L M))");

// ============================================================
// Genericity Laws
// ============================================================
//
// Genericity means that algebraic operations push any surrounding context into their continuation parameters.
// These laws are the actual markers of continuation parameters, 
// whereas the "continue:" label is just optics.
// Note that "raise" does not have a genericity law, as it has no continuation.

axiom("get_gen",
    "equals (F[get continue: (s. K[s])]) (get continue: (s. F[K[s]]))");

axiom("put_gen",
    "equals (F[put v continue: K]) (put v continue: F[K])");

axiom("choose_gen",
    "equals (F[choose continue: K L]) (choose continue: F[K] F[L])");

// ============================================================
// Derived: put-get-id
// ============================================================
//
// Evaluating get in the argument position of put reads the
// current state and stores it back — a no-op.
//
//   put (get continue: (s. s)) continue: K  =  K
//
// Proof: float get out of the argument via get_gen,
//        then apply get-put.

function provePutGetId() : Thm {
    // get_gen: equals (F[get continue: (s. K[s])]) (get continue: (s. F[K[s]]))
    // Substitute K(arity 1) -> (s. s)  and  F(arity 1) -> (x. put x continue: K)
    // Result: equals (put (get continue: (s. s)) continue: K) (get continue: (s. put s continue: K))
    const step1 = subst(S("K", "(s. s)", "F", "(x. put x continue: K)"), thm("get_gen"));

    // get-put: equals (get continue: (s. put s continue: K)) K
    const step2 = thm("get-put");

    // Transitivity
    return equalsTrans(step1, step2);
}

have("put-get-id",
    "equals (put (get continue: (s. s)) continue: K) K", [],
    provePutGetId());

// ============================================================
// Derived: get-raise
// ============================================================
//
// A get whose result is ignored (here by raise) is a no-op.
// This follows from get's genericity alone — no axioms on
// raise are needed.
//
//   get continue: (s. raise e continue:)  =  raise e continue:
//
// Proof: instantiate get_gen with K = identity and
//        F = constant (raise e continue:), then flip.

function proveGetRaise() : Thm {
    // get_gen: equals (F[get continue: (s. K[s])]) (get continue: (s. F[K[s]]))
    // Substitute K(arity 1) -> (s. s) and F(arity 1) -> (x. raise e continue:)
    // Result: equals (raise e continue:) (get continue: (s. raise e continue:))
    const step1 = subst(S("K", "(s. s)", "F", "(x. raise e continue:)"), thm("get_gen"));

    // Flip to get the desired direction
    return equalsSym(step1);
}

have("get-raise",
    "equals (get continue: (s. raise e continue:)) (raise e continue:)", [],
    proveGetRaise());

// ============================================================
// Derived: get-const
// ============================================================
//
// A get whose continuation ignores the state is a no-op.
// This is what it means for get to be an "effect": it has
// no observable consequence unless its result is used.
//
//   get continue: (s. K)  =  K
//
// Proof: same as get-raise, but with arbitrary K instead of
//        raise e continue:.

function proveGetConst() : Thm {
    // get_gen with K(arity 1) -> (s. s) and F(arity 1) -> (x. K)
    // LHS: F[get continue: (s. s)] = K
    // RHS: get continue: (s. F[s]) = get continue: (s. K)
    // Result: equals K (get continue: (s. K))
    const step1 = subst(S("K", "(s. s)", "F", "(x. K)"), thm("get_gen"));

    return equalsSym(step1);
}

have("get-const",
    "equals (get continue: (s. K)) K", [],
    proveGetConst());

// ============================================================
// Derived: get-raise-state
// ============================================================
//
// Reading the state and then raising it as an exception is the
// same as raising the-result-of-reading-the-state.
// The get floats out of the continuation into the argument of raise.
//
//   get continue: (s. raise s continue:)  =  raise (get continue: (s. s)) continue:

function proveGetRaiseState() : Thm {
    // get_gen with K(arity 1) -> (s. s) and F(arity 1) -> (x. raise x continue:)
    // LHS: raise (get continue: (s. s)) continue:
    // RHS: get continue: (s. raise s continue:)
    const step1 = subst(S("K", "(s. s)", "F", "(x. raise x continue:)"), thm("get_gen"));

    return equalsSym(step1);
}

have("get-raise-state",
    "equals (get continue: (s. raise s continue:)) (raise (get continue: (s. s)) continue:)", [],
    proveGetRaiseState());

endTheory("Algebraic-Effects");


