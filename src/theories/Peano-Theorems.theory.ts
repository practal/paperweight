import { Term } from "../kernel/index.js";
import { beginTheory, endTheory, have, thm, S, subst, Thm, includeTheory, conjecture, infer, conclOf } from "../workbench.js";
import "./Peano-Recursion.theory.js";
import { substEquals, equalsSym, equalsTrans, congr, conditionalCongr, conditionalEqualsTrans, equalsRefl, destEquals } from "./Equality.theory.js";
import { modusPonens, impliesTrans, conditionalModusPonens, impliesExchange, weaken, conditionalImpliesTrans, destImplies } from "./Implication.theory.js";
import { inductNat } from "./Peano.theory.js";
import { app, lam, provePureImplication, tyAtom, tyImp, v } from "../proof-tools/pure-implication.js";

beginTheory();
includeTheory("Peano-Primitive-Recursion");

have("Nat-one", "Nat one", [], proveNatOne());
have("add-zero", "equals (add zero n) n", [], proveAddZero());
have("add-succ", "implies (Nat n) (equals (add (succ n) m) (succ (add n m)))", [], proveAddSucc());

// Closure: Nat is closed under addition
have("Nat-add", "implies (Nat n) (implies (Nat m) (Nat (add n m)))", [], proveNatAdd());

// Right-identity and right-successor for add
have("add-zero-right", "implies (Nat n) (equals (add n zero) n)", [], proveAddZeroRight());
have("add-succ-right", "implies (Nat n) (equals (add n (succ m)) (succ (add n m)))", [], proveAddSuccRight());

// Commutativity and associativity of addition
have("add-comm", "implies (Nat n) (implies (Nat m) (equals (add n m) (add m n)))", [], proveAddComm());
have("add-assoc", "implies (Nat n) (implies (Nat m) (implies (Nat k) (equals (add (add n m) k) (add n (add m k)))))", [], proveAddAssoc());

// Multiplication properties
have("mul-zero-left", "equals (mul zero n) zero", [], proveMulZeroLeft());
have("mul-zero", "implies (Nat n) (equals (mul n zero) zero)", [], proveMulZero());
have("mul-succ-left", "implies (Nat n) (equals (mul (succ n) m) (add (mul n m) m))", [], mulSuccLeft());
have("Nat-mul", "implies (Nat n) (implies (Nat m) (Nat (mul n m)))", [], proveNatMul());
have("mul-succ", "implies (Nat n) (implies (Nat m) (equals (mul n (succ m)) (add (mul n m) n)))", [], proveMulSucc());
have("mul-one-left", "equals (mul one n) n", [], proveMulOneLeft());
have("mul-one-right", "implies (Nat n) (equals (mul n one) n)", [], proveMulOneRight());
have("mul-comm", "implies (Nat n) (implies (Nat m) (equals (mul n m) (mul m n)))", [], proveMulComm());
have("mul-distr-right", "implies (Nat n) (implies (Nat m) (implies (Nat k) (equals (mul n (add m k)) (add (mul n m) (mul n k)))))", [], proveMulDistrRight());
have("mul-assoc", "implies (Nat n) (implies (Nat m) (implies (Nat k) (equals (mul (mul n m) k) (mul n (mul m k)))))", [], proveMulAssoc());

endTheory("Peano-Theorems");

// implies (Nat n) (equals (add (succ n) m) (succ (add n m)))
function proveAddSucc() : Thm {
    // primrec-succ: implies (Nat n) (equals (primrec (succ n) m (i u. succ u)) (succ (primrec n m (i u. succ u))))
    const primrecSucc = subst(S("g", "m", "h", "i u. succ u"), thm("primrec-succ"));
    // rewrite LHS: primrec (succ n) m ... → add (succ n) m
    const addDefSucc = subst(S("n", "succ n"), thm("add_def"));
    const rewriterLHS = subst(S("A", "t. equals t (succ (primrec n m (i u. succ u)))"),
        substEquals(equalsSym(addDefSucc)));
    const step2 = impliesTrans(primrecSucc, rewriterLHS);
    // rewrite RHS: primrec n m ... → add n m
    const rewriterRHS = subst(S("A", "t. equals (add (succ n) m) (succ t)"),
        substEquals(equalsSym(thm("add_def"))));
    return impliesTrans(step2, rewriterRHS);
}

// equals (add zero n) n: unfold add via primrec-zero, rewrite back
function proveAddZero() : Thm {
    // primrec-zero: equals (primrec zero n (i u. succ u)) n  (no premises, unchanged)
    const primrecZero = subst(S("g", "n", "h", "i u. succ u"), thm("primrec-zero"));
    // add_def: equals (add zero n) (primrec zero n (i u. succ u))
    const addDef = subst(S("n", "zero", "m", "n"), thm("add_def"));
    // rewrite: implies (equals (primrec...) n) (equals (add zero n) n)
    const rewriter = subst(S("A", "t. equals t n"), substEquals(equalsSym(addDef)));
    return modusPonens(rewriter, primrecZero);
}

// Nat one: from Nat-zero + Nat-succ, then rewrite succ zero → one via one_def
function proveNatOne() : Thm {
    // Nat-succ is now: implies (Nat n) (Nat (succ n))
    const natSuccZero = modusPonens(subst(S("n", "zero"), thm("Nat-succ")), thm("Nat-zero"));
    // rewrite: implies (Nat (succ zero)) (Nat one)
    const rewriter = subst(S("A", "n. Nat n"), substEquals(equalsSym(thm("one_def"))));
    return modusPonens(rewriter, natSuccZero);
}

// implies (Nat n) (equals (add n (succ m)) (succ (add n m))): induction on n
function proveAddSuccRight() : Thm {
    // Base: equals (add zero (succ m)) (succ m) = succ (add zero m)
    const base = equalsTrans(
        subst(S("n", "succ m"), thm("add-zero")),
        congr(equalsSym(subst(S("n", "m"), thm("add-zero"))), "t. succ t"));
    const step = proveAddSuccRightStep();
    return inductNat("n. equals (add n (succ m)) (succ (add n m))", step, base);
}

function proveAddSuccRightStep() : Thm {
    // Goal: implies (Nat n) (implies IH (equals (add (succ n) (succ m)) (succ (add (succ n) m))))
    // where IH = equals (add n (succ m)) (succ (add n m))

    // Part 1: implies (Nat n) (implies IH (equals (add (succ n) (succ m)) (succ (succ (add n m)))))
    // add-succ[m→succ m] then rewrite via IH under succ
    const addSuccLHS = subst(S("m", "succ m"), thm("add-succ"));
    const ihRewrite = subst(
        S("x", "add n (succ m)", "y", "succ (add n m)", "A", "t. equals (add (succ n) (succ m)) (succ t)"),
        thm("equals_subst"));
    const part1 = impliesTrans(addSuccLHS, impliesExchange(ihRewrite));

    // Part 2: implies (Nat n) (equals (succ (succ (add n m))) (succ (add (succ n) m)))
    // add-succ sym under succ congruence
    const addSuccSym = impliesTrans(thm("add-succ"),
        subst(S("x", "add (succ n) m", "y", "succ (add n m)"), thm("equals_sym")));
    const part2 = conditionalCongr(addSuccSym, "t. succ t");

    // Bridge: from part2 (Nat n → equals b c), build (Nat n → (equals a b → equals a c))
    // using equals_subst with template "t. equals (add (succ n) (succ m)) t"
    const bridge = impliesTrans(part2, subst(
        S("x", "succ (succ (add n m))", "y", "succ (add (succ n) m)",
          "A", "t. equals (add (succ n) (succ m)) t"),
        thm("equals_subst")));
    // Combine: part1 = Nat n → (IH → equals a b), bridge = Nat n → (equals a b → equals a c)
    // Result: Nat n → (IH → equals a c)
    return conditionalImpliesTrans(part1, bridge);
}

// implies (Nat n) (equals (add n zero) n): induction on n
function proveAddZeroRight() : Thm {
    // Base case: equals (add zero zero) zero
    const base = subst(S("n", "zero"), thm("add-zero"));

    // Induction step: implies (Nat n) (implies (equals (add n zero) n) (equals (add (succ n) zero) (succ n)))
    const addSuccZero = subst(S("m", "zero"), thm("add-succ"));
    const eqRewrite = subst(
        S("x", "add n zero", "y", "n", "A", "t. equals (add (succ n) zero) (succ t)"),
        thm("equals_subst"));
    const step = impliesTrans(addSuccZero, impliesExchange(eqRewrite));

    return inductNat("n. equals (add n zero) n", step, base);
}

// implies (Nat n) (implies (Nat m) (Nat (add n m))): induction on n
function proveNatAdd() : Thm {
    // Base case: implies (Nat m) (Nat (add zero m))
    const base = subst(S("A", "n. Nat n"),
        substEquals(equalsSym(subst(S("n", "m"), thm("add-zero")))));

    // Induction step: implies (Nat n) (implies IH (implies (Nat m) (Nat (add (succ n) m))))
    const addSuccSym = impliesTrans(thm("add-succ"),
        subst(S("x", "add (succ n) m", "y", "succ (add n m)"), thm("equals_sym")));
    const eqSubstInst = subst(S("x", "succ (add n m)", "y", "add (succ n) m", "A", "t. Nat t"),
        thm("equals_subst"));
    const natN_to_rewrite = impliesTrans(addSuccSym, eqSubstInst);
    const natSuccAdd = subst(S("n", "add n m"), thm("Nat-succ"));
    const natN_to_chain = impliesExchange(
        impliesTrans(natSuccAdd, impliesExchange(natN_to_rewrite)));
    const k_inst = subst(
        S("A", "implies (Nat (add n m)) (Nat (add (succ n) m))", "B", "Nat m"),
        thm("implies_1"));
    const s_inst = subst(
        S("A", "Nat m", "B", "Nat (add n m)", "C", "Nat (add (succ n) m)"),
        thm("implies_2"));
    const step = impliesTrans(natN_to_chain, impliesTrans(k_inst, s_inst));

    return inductNat("n. implies (Nat m) (Nat (add n m))", step, base);
}

// implies (Nat n) (implies (Nat m) (equals (add n m) (add m n)))
function proveAddComm() : Thm {
    const base = proveAddCommBase();
    const step = proveAddCommStep();
    return inductNat("n. implies (Nat m) (equals (add n m) (add m n))", step, base);
}

// Base: implies (Nat m) (equals (add zero m) (add m zero))
function proveAddCommBase() : Thm {
    // From add-zero[n→m]: equals (add zero m) m
    // equalsSym: equals m (add zero m)
    // substEquals: implies A[m] A[add zero m]
    // With A = t. equals t (add m zero): implies (equals m (add m zero)) (equals (add zero m) (add m zero))
    const rewriter = subst(S("A", "t. equals t (add m zero)"),
        substEquals(equalsSym(subst(S("n", "m"), thm("add-zero")))));
    // From add-zero-right[n→m] + equalsSym: implies (Nat m) (equals m (add m zero))
    const natm_to_eq = impliesTrans(
        subst(S("n", "m"), thm("add-zero-right")),
        subst(S("x", "add m zero", "y", "m"), thm("equals_sym")));
    return impliesTrans(natm_to_eq, rewriter);
}

// Step: implies (Nat n) (implies IH GOAL)
// where IH = implies (Nat m) (equals (add n m) (add m n))
//       GOAL = implies (Nat m) (equals (add (succ n) m) (add m (succ n)))
function proveAddCommStep() : Thm {
    // --- Congruence: implies (equals (add n m) (add m n)) (equals (succ (add n m)) (succ (add m n))) ---
    const congSubst = subst(
        S("x", "add n m", "y", "add m n", "A", "t. equals (succ (add n m)) (succ t)"),
        thm("equals_subst"));
    const congStep = conditionalModusPonens(congSubst,
        weaken(equalsRefl("succ (add n m)"), "equals (add n m) (add m n)"));

    // --- add-succ-right reversed: implies (Nat m) (equals (succ (add m n)) (add m (succ n))) ---
    const addSuccRightSym = impliesTrans(
        subst(S("n", "m", "m", "n"), thm("add-succ-right")),
        subst(S("x", "add m (succ n)", "y", "succ (add m n)"), thm("equals_sym")));

    // --- Chain congStep and addSuccRightSym under Nat m ---
    // implies (Nat m) (implies (equals (succ (add n m)) (succ (add m n))) (equals (succ (add n m)) (add m (succ n))))
    const natm_to_trans = impliesTrans(addSuccRightSym,
        subst(S("x", "succ (add m n)", "y", "add m (succ n)", "A", "t. equals (succ (add n m)) t"),
            thm("equals_subst")));
    // implies (Nat m) (implies EQ (equals (succ (add n m)) (add m (succ n))))
    const chain23 = conditionalImpliesTrans(weaken(congStep, "Nat m"), natm_to_trans);

    // --- add-succ symmed: implies (Nat n) (equals (succ (add n m)) (add (succ n) m)) ---
    const addSuccSymmed = impliesTrans(thm("add-succ"),
        subst(S("x", "add (succ n) m", "y", "succ (add n m)"), thm("equals_sym")));

    // --- Rewriter: implies (Nat n) (implies (equals (succ (add n m)) (add m (succ n))) (equals (add (succ n) m) (add m (succ n)))) ---
    const rewriter1 = impliesTrans(addSuccSymmed,
        subst(S("x", "succ (add n m)", "y", "add (succ n) m", "A", "t. equals t (add m (succ n))"),
            thm("equals_subst")));

    // --- K+S to extend chain23 with rewriter1 ---
    // K: implies (implies Y Z) (implies EQ (implies Y Z))
    const k_inst = subst(S("A",
        "implies (equals (succ (add n m)) (add m (succ n))) (equals (add (succ n) m) (add m (succ n)))",
        "B", "equals (add n m) (add m n)"), thm("implies_1"));
    // S: implies (implies EQ (implies Y Z)) (implies (implies EQ Y) (implies EQ Z))
    const s_inst = subst(S("A", "equals (add n m) (add m n)",
        "B", "equals (succ (add n m)) (add m (succ n))",
        "C", "equals (add (succ n) m) (add m (succ n))"), thm("implies_2"));
    // implies (Nat n) (implies (implies EQ Y) (implies EQ Z))
    const natn_eqy_to_eqz = impliesTrans(rewriter1, impliesTrans(k_inst, s_inst));

    // --- Combine chain23 and natn_eqy_to_eqz ---
    // Exchange: implies (implies EQ Y) (implies (Nat n) (implies EQ Z))
    const exchanged = impliesExchange(natn_eqy_to_eqz);
    // implies (Nat m) (implies (Nat n) (implies EQ Z))
    const combined = impliesTrans(chain23, exchanged);
    // implies (Nat n) (implies (Nat m) (implies EQ Z))
    const stepA = impliesExchange(combined);

    // --- S combinator on Nat m to get implies (Nat n) (implies IH GOAL) ---
    const s_natm = subst(S("A", "Nat m",
        "B", "equals (add n m) (add m n)",
        "C", "equals (add (succ n) m) (add m (succ n))"), thm("implies_2"));
    return impliesTrans(stepA, s_natm);
}

// Helper: given th with conclusion implies H (implies X Y),
// returns implies H (implies (implies C X) (implies C Y))
function liftRewriter(th: Thm, c: string) : Thm {
    const [_h, inner] = destImplies(conclOf(th));
    const [x, y] = destImplies(inner);
    const k = subst(S("A", inner, "B", c), thm("implies_1"));
    const s = subst(S("A", c, "B", x, "C", y), thm("implies_2"));
    return impliesTrans(th, impliesTrans(k, s));
}

// implies (Nat n) (implies (Nat m) (implies (Nat k) (equals (add (add n m) k) (add n (add m k)))))
function proveAddAssoc() : Thm {
    const base = proveAddAssocBase();
    const step = proveAddAssocStep();
    return inductNat("n. implies (Nat m) (implies (Nat k) (equals (add (add n m) k) (add n (add m k))))", step, base);
}

// Base: implies (Nat m) (implies (Nat k) (equals (add (add zero m) k) (add zero (add m k))))
function proveAddAssocBase() : Thm {
    const lhs = congr(subst(S("n", "m"), thm("add-zero")), "t. add t k");
    const rhs = equalsSym(subst(S("n", "add m k"), thm("add-zero")));
    const eq = equalsTrans(lhs, rhs);
    return weaken(weaken(eq, "Nat k"), "Nat m");
}

// Step: implies (Nat n) (implies IH GOAL)
function proveAddAssocStep() : Thm {
    const core = proveAddAssocCore();
    // core: implies (Nat n) (implies (Nat m) (implies IH_eq GOAL_eq))
    // Lift through Nat k and Nat m to get implies (Nat n) (implies IH GOAL)
    const [_natn, coreInner1] = destImplies(conclOf(core));
    const [_natm, coreInner2] = destImplies(coreInner1);
    const [ih_eq, goal_eq] = destImplies(coreInner2);

    // lift_k: implies (implies IH_eq GOAL_eq) (implies (implies (Nat k) IH_eq) (implies (Nat k) GOAL_eq))
    const k_k = subst(S("A", coreInner2, "B", "Nat k"), thm("implies_1"));
    const s_k = subst(S("A", "Nat k", "B", ih_eq, "C", goal_eq), thm("implies_2"));
    const lift_k = impliesTrans(k_k, s_k);

    // lift_km: implies (implies (Nat m) (implies IH_eq GOAL_eq)) (implies (Nat m) (...))
    const [_lk_a, lk_c] = destImplies(conclOf(lift_k));
    const k_m = subst(S("A", conclOf(lift_k), "B", "Nat m"), thm("implies_1"));
    const s_m = subst(S("A", "Nat m", "B", coreInner2, "C", lk_c), thm("implies_2"));
    const lift_km = modusPonens(impliesTrans(k_m, s_m), lift_k);

    const after_lift = impliesTrans(core, lift_km);

    // S on Nat m
    const [lk_a2, lk_c2] = destImplies(lk_c);
    const s_m2 = subst(S("A", "Nat m", "B", lk_a2, "C", lk_c2), thm("implies_2"));
    return impliesTrans(after_lift, s_m2);
}

// Core: implies (Nat n) (implies (Nat m) (implies IH_eq GOAL_eq))
function proveAddAssocCore() : Thm {
    // E1: implies (Nat n) (equals (add (add (succ n) m) k) (add (succ (add n m)) k))
    const e1 = conditionalCongr(thm("add-succ"), "t. add t k");

    // E2: implies (Nat n) (implies (Nat m) (equals (add (succ (add n m)) k) (succ (add (add n m) k))))
    const e2_raw = subst(S("n", "add n m", "m", "k"), thm("add-succ"));
    const e2 = conditionalImpliesTrans(thm("Nat-add"), weaken(e2_raw, "Nat n"));

    // E3: implies IH_eq (equals (succ (add (add n m) k)) (succ (add n (add m k))))
    const e3 = conditionalModusPonens(
        subst(S("x", "add (add n m) k", "y", "add n (add m k)",
              "A", "t. equals (succ (add (add n m) k)) (succ t)"),
            thm("equals_subst")),
        weaken(equalsRefl("succ (add (add n m) k)"),
            "equals (add (add n m) k) (add n (add m k))"));

    // E4: implies (Nat n) (equals (succ (add n (add m k))) (add (succ n) (add m k)))
    const e4 = impliesTrans(
        subst(S("m", "add m k"), thm("add-succ")),
        subst(S("x", "add (succ n) (add m k)", "y", "succ (add n (add m k))"), thm("equals_sym")));

    // Chain E2+E3 → E23
    const e23_bridge = subst(
        S("x", "succ (add (add n m) k)", "y", "succ (add n (add m k))",
          "A", "t. equals (add (succ (add n m)) k) t"),
        thm("equals_subst"));
    const e23_chain = impliesExchange(impliesTrans(e3, e23_bridge));
    const e23 = conditionalImpliesTrans(e2, weaken(e23_chain, "Nat n"));

    // Chain E23+E4: lift E4 rewriter through IH_eq and Nat m
    const e4_bridge = subst(
        S("x", "succ (add n (add m k))", "y", "add (succ n) (add m k)",
          "A", "t. equals (add (succ (add n m)) k) t"),
        thm("equals_subst"));
    const e4_rewriter = impliesTrans(e4, e4_bridge);
    const e4_lifted = liftRewriter(liftRewriter(e4_rewriter,
        "equals (add (add n m) k) (add n (add m k))"), "Nat m");
    const e234 = conditionalModusPonens(e4_lifted, e23);

    // Chain E1+E234: lift E1 rewriter through IH_eq and Nat m
    const e1_sym = impliesTrans(e1,
        subst(S("x", "add (add (succ n) m) k", "y", "add (succ (add n m)) k"), thm("equals_sym")));
    const e1_bridge = subst(
        S("x", "add (succ (add n m)) k", "y", "add (add (succ n) m) k",
          "A", "t. equals t (add (succ n) (add m k))"),
        thm("equals_subst"));
    const e1_rewriter = impliesTrans(e1_sym, e1_bridge);
    const e1_lifted = liftRewriter(liftRewriter(e1_rewriter,
        "equals (add (add n m) k) (add n (add m k))"), "Nat m");
    return conditionalModusPonens(e1_lifted, e234);
}

// implies (Nat n) (equals (mul n zero) zero)
function proveMulZeroLeft() : Thm {
    return equalsTrans(
        subst(S("n", "zero", "m", "n"), thm("mul_def")),
        subst(S("g", "zero", "h", "i u. add u n"), thm("primrec-zero")));
}

// implies (Nat n) (equals (mul n zero) zero)
function proveMulZero() : Thm {
    const base = equalsTrans(
        subst(S("n", "zero", "m", "zero"), thm("mul_def")),
        subst(S("g", "zero", "h", "i u. add u zero"), thm("primrec-zero")));
    const step = proveMulZeroStep();
    return inductNat("n. equals (mul n zero) zero", step, base);
}

function proveMulZeroStep() : Thm {
    // mulSuccZ: implies (Nat n) (equals (mul (succ n) zero) (add (mul n zero) zero))
    const ps = subst(S("g", "zero", "h", "i u. add u zero"), thm("primrec-succ"));
    const rwLHS = subst(S("A", "t. equals t (add (primrec n zero (i u. add u zero)) zero)"),
        substEquals(equalsSym(subst(S("n", "succ n", "m", "zero"), thm("mul_def")))));
    const rwRHS = subst(S("A", "t. equals (mul (succ n) zero) (add t zero)"),
        substEquals(equalsSym(subst(S("m", "zero"), thm("mul_def")))));
    const mulSuccZ = impliesTrans(impliesTrans(ps, rwLHS), rwRHS);

    // ihCongr: implies IH (equals (add (mul n zero) zero) (add zero zero))
    const ihCongr = conditionalModusPonens(
        subst(S("x", "mul n zero", "y", "zero",
              "A", "t. equals (add (mul n zero) zero) (add t zero)"),
            thm("equals_subst")),
        weaken(equalsRefl("add (mul n zero) zero"), "equals (mul n zero) zero"));

    // ihChain: implies IH (equals (add (mul n zero) zero) zero)
    const ihChain = impliesTrans(ihCongr,
        subst(S("A", "t. equals (add (mul n zero) zero) t"),
            substEquals(subst(S("n", "zero"), thm("add-zero")))));

    // Combine: implies (Nat n) (implies IH (equals (mul (succ n) zero) zero))
    const bridge = subst(
        S("x", "add (mul n zero) zero", "y", "zero",
          "A", "t. equals (mul (succ n) zero) t"),
        thm("equals_subst"));
    return impliesTrans(mulSuccZ, impliesExchange(impliesTrans(ihChain, bridge)));
}

// Pure formula: implies (implies A (implies B C)) (implies B (implies A C))
function exchangeFormula() : Thm {
    // K_BA: implies B (implies A B)
    const k_ba = subst(S("A", "B", "B", "A"), thm("implies_1"));
    // step3: implies (implies (implies A B) (implies A C)) (implies B (implies A B))
    const step3 = weaken(k_ba, "implies (implies A B) (implies A C)");
    // step5: implies (implies (implies A B) (implies A C)) (implies B (implies (implies A B) (implies A C)))
    const step5 = subst(S("A", "implies (implies A B) (implies A C)", "B", "B"), thm("implies_1"));
    // step4: implies (implies B (implies (implies A B) (implies A C))) (implies (implies B (implies A B)) (implies B (implies A C)))
    const step4 = subst(S("A", "B", "B", "implies A B", "C", "implies A C"), thm("implies_2"));
    // step6: implies (implies (implies A B) (implies A C)) (implies (implies B (implies A B)) (implies B (implies A C)))
    const step6 = impliesTrans(step5, step4);
    // qr: implies (implies (implies A B) (implies A C)) (implies B (implies A C))
    const qr = conditionalModusPonens(step6, step3);
    // Chain with S: implies (implies A (implies B C)) (implies B (implies A C))
    return impliesTrans(thm("implies_2"), qr);
}

// Given th: implies H (implies A (implies B C))
// Returns: implies H (implies B (implies A C))
function innerExchange(th: Thm) : Thm {
    const [_h, abc] = destImplies(conclOf(th));
    const [a, bc] = destImplies(abc);
    const [b, c] = destImplies(bc);
    const ef = exchangeFormula();
    const ef_inst = subst(S("A", a, "B", b, "C", c), ef);
    return impliesTrans(th, ef_inst);
}

// implies (Nat n) (equals (mul (succ n) m) (add (mul n m) m))
function mulSuccLeft() : Thm {
    // primrec-succ[g:=zero, h:="i u. add u m"]:
    // implies (Nat n) (equals (primrec (succ n) zero (i u. add u m)) (add (primrec n zero (i u. add u m)) m))
    const ps = subst(S("g", "zero", "h", "i u. add u m"), thm("primrec-succ"));
    // Rewrite LHS: primrec (succ n) zero (i u. add u m) → mul (succ n) m
    const mulDefSuccN = subst(S("n", "succ n"), thm("mul_def"));
    const rwLHS = subst(S("A", "t. equals t (add (primrec n zero (i u. add u m)) m)"),
        substEquals(equalsSym(mulDefSuccN)));
    const step1 = impliesTrans(ps, rwLHS);
    // Rewrite RHS: primrec n zero (i u. add u m) → mul n m
    const rwRHS = subst(S("A", "t. equals (mul (succ n) m) (add t m)"),
        substEquals(equalsSym(thm("mul_def"))));
    return impliesTrans(step1, rwRHS);
}

// equals (mul one n) n
function proveMulOneLeft() : Thm {
    const oneToSuccZero = congr(thm("one_def"), "t. mul t n");
    const succZeroCase = modusPonens(subst(S("n", "zero", "m", "n"), mulSuccLeft()), thm("Nat-zero"));
    const zeroLeftUnderAdd = congr(thm("mul-zero-left"), "t. add t n");
    const addZero = subst(S("n", "n"), thm("add-zero"));
    return equalsTrans(oneToSuccZero,
        equalsTrans(succZeroCase, equalsTrans(zeroLeftUnderAdd, addZero)));
}

function addOneRight() : Thm {
    const eq1 = weaken(congr(thm("one_def"), "t. add n t"), "Nat n");
    const eq2 = subst(S("m", "zero"), thm("add-succ-right"));
    const eq3 = conditionalCongr(thm("add-zero-right"), "t. succ t");
    const bridge12 = impliesTrans(
        eq2,
        subst(S("x", "add n (succ zero)", "y", "succ (add n zero)",
              "A", "t. equals (add n one) t"),
            thm("equals_subst")));
    const eq12 = conditionalModusPonens(bridge12, eq1);

    const bridge123 = impliesTrans(
        eq3,
        subst(S("x", "succ (add n zero)", "y", "succ n",
              "A", "t. equals (add n one) t"),
            thm("equals_subst")));
    return conditionalModusPonens(bridge123, eq12);
}

// implies (Nat n) (equals (mul n one) n)
function proveMulOneRight() : Thm {
    const base = subst(S("n", "one"), thm("mul-zero-left"));
    const step = proveMulOneRightStep();
    return inductNat("n. equals (mul n one) n", step, base);
}

function proveMulOneRightStep() : Thm {
    const mulSuccOne = subst(S("m", "one"), thm("mul-succ-left"));

    const ihUnderAdd = conditionalModusPonens(
        subst(S("x", "mul n one", "y", "n",
              "A", "t. equals (add (mul n one) one) (add t one)"),
            thm("equals_subst")),
        weaken(equalsRefl("add (mul n one) one"), "equals (mul n one) n"));

    const mulSuccBridge = impliesExchange(impliesTrans(ihUnderAdd,
        subst(S("x", "add (mul n one) one", "y", "add n one",
              "A", "t. equals (mul (succ n) one) t"),
            thm("equals_subst"))));
    const part1 = impliesTrans(mulSuccOne, mulSuccBridge);

    const addOneBridge = impliesTrans(
        addOneRight(),
        subst(S("x", "add n one", "y", "succ n",
              "A", "t. equals (mul (succ n) one) t"),
            thm("equals_subst")));

    return conditionalImpliesTrans(part1, addOneBridge);
}

// implies (Nat n) (implies (Nat m) (equals (mul n m) (mul m n))): induction on n
function proveMulComm() : Thm {
    const base = proveMulCommBase();
    const step = proveMulCommStep();
    return inductNat("n. implies (Nat m) (equals (mul n m) (mul m n))", step, base);
}

// Base: implies (Nat m) (equals (mul zero m) (mul m zero))
function proveMulCommBase() : Thm {
    const left = weaken(subst(S("n", "m"), thm("mul-zero-left")), "Nat m");
    const right = impliesTrans(
        subst(S("n", "m"), thm("mul-zero")),
        subst(S("x", "mul m zero", "y", "zero"), thm("equals_sym")),
    );
    return conditionalEqualsTrans(left, right);
}

// Informal induction idea for mul-comm.
//
// We induct on n. The base case is immediate from the zero laws:
//   mul zero m = zero = mul m zero.
//
// For the step, assume the induction hypothesis
//   IH: mul n m = mul m n.
// Then expand on the left:
//   mul (succ n) m
//   = add (mul n m) m.
// Rewrite the inner multiplication using IH:
//   = add (mul m n) m.
// Finally fold that back using the right-successor law:
//   = mul m (succ n).
//
// As with mul-succ, the arithmetic part is short. Most of the formal work is
// threading the equalities through the shared assumptions Nat n and Nat m.
function proveMulCommStep() : Thm {
    const core = proveMulCommCore();
    const [_natn, inner1] = destImplies(conclOf(core));
    const [_natm, inner2] = destImplies(inner1);
    const [ih_eq, _goal_eq] = destImplies(inner2);

    const s_m = subst(S("A", "Nat m", "B", ih_eq, "C",
        "equals (mul (succ n) m) (mul m (succ n))"), thm("implies_2"));
    return impliesTrans(core, s_m);
}

// Core: implies (Nat n) (implies (Nat m) (implies IH_eq (equals (mul (succ n) m) (mul m (succ n)))))
function proveMulCommCore() : Thm {
    // E1: implies (Nat n) (implies (Nat m) (equals (mul (succ n) m) (add (mul n m) m)))
    const e1 = impliesExchange(weaken(thm("mul-succ-left"), "Nat m"));

    // E2: IH_eq rewrites the inner multiplication under add _ m.
    const e2 = conditionalModusPonens(
        subst(S("x", "mul n m", "y", "mul m n",
              "A", "t. equals (add (mul n m) m) (add t m)"),
            thm("equals_subst")),
        weaken(equalsRefl("add (mul n m) m"), "equals (mul n m) (mul m n)"));
    const bridge12 = subst(
        S("x", "add (mul n m) m", "y", "add (mul m n) m",
          "A", "t. equals (mul (succ n) m) t"),
        thm("equals_subst"));
    const e2to = impliesTrans(e2, bridge12);
    const e2x = impliesExchange(e2to);
    const e12 = modusPonens(
        liftFormulaThrough(liftFormulaThrough(e2x, "Nat m"), "Nat n"),
        e1,
    );

    // E3: mul m (succ n) = add (mul m n) m, then flip the equality.
    const mulSuccRight = impliesExchange(subst(S("n", "m", "m", "n"), thm("mul-succ")));
    const sym = subst(S("x", "mul m (succ n)", "y", "add (mul m n) m"), thm("equals_sym"));
    const e3 = conditionalModusPonens(
        liftRewriter(weaken(sym, "Nat n"), "Nat m"),
        mulSuccRight,
    );

    // Use E3 to rewrite the RHS of E12.
    const finalBridge0 = subst(
        S("x", "add (mul m n) m", "y", "mul m (succ n)",
          "A", "t. equals (mul (succ n) m) t"),
        thm("equals_subst"));
    const finalBridge = modusPonens(
        liftFormulaThrough(liftFormulaThrough(finalBridge0, "Nat m"), "Nat n"),
        e3,
    );
    return chainImp2(e12, finalBridge);
}

// implies (Nat n) (implies (Nat m) (implies (Nat k) (equals (mul n (add m k)) (add (mul n m) (mul n k)))))
function proveMulDistrRight() : Thm {
    const byK = inductNat(
        "k. implies (Nat x) (implies (Nat m) (equals (mul x (add m k)) (add (mul x m) (mul x k))))",
        subst(S("n", "x", "k", "n"), proveMulDistrRightStep()),
        subst(S("n", "x"), proveMulDistrRightBase()),
    );
    // Reorder the induction variable back to the theorem's public argument order n, m, k.
    return subst(S("x", "n", "n", "k"), innerExchange(impliesExchange(byK)));
}

// Base: implies (Nat n) (implies (Nat m) (equals (mul n (add m zero)) (add (mul n m) (mul n zero))))
function proveMulDistrRightBase() : Thm {
    const lhs0 = conditionalCongr(subst(S("n", "m"), thm("add-zero-right")), "t. mul n t");
    const lhs = weaken(lhs0, "Nat n");

    const rhs0 = conditionalCongr(thm("mul-zero"), "t. add (mul n m) t");
    const rhs0sym = impliesTrans(
        rhs0,
        subst(S("x", "add (mul n m) (mul n zero)", "y", "add (mul n m) zero"), thm("equals_sym")),
    );
    const rhs = impliesExchange(weaken(rhs0sym, "Nat m"));

    const addZero0 = subst(S("n", "mul n m"), thm("add-zero-right"));
    const addZeroSym0 = impliesTrans(
        addZero0,
        subst(S("x", "add (mul n m) zero", "y", "mul n m"), thm("equals_sym")),
    );
    const addZero1 = weaken(addZeroSym0, "Nat n");
    const addZero = conditionalModusPonens(
        liftRewriter(addZero1, "Nat m"),
        thm("Nat-mul"),
    );

    return chainEqNM(lhs, chainEqNM(addZero, rhs));
}

// Informal induction idea for mul-distr-right.
//
// It is cleaner to induct on k, not on n.
//
// Base:
//   mul n (add m zero) = mul n m = add (mul n m) (mul n zero).
//
// Step:
//   mul n (add m (succ k))
//   = mul n (succ (add m k))                   [add-succ-right]
//   = add (mul n (add m k)) n                  [mul-succ]
//   = add (add (mul n m) (mul n k)) n          [IH]
//   = add (mul n m) (add (mul n k) n)          [add-assoc]
//   = add (mul n m) (mul n (succ k)).          [mul-succ]
//
// This proof is the first place where the three shared assumptions Nat n,
// Nat m, Nat k really matter, so it is where the 3-context proof tools pay off.
function proveMulDistrRightStep() : Thm {
    const core = impliesExchange(innerExchange(proveMulDistrRightCore()));
    return packageStepOver2Hyps(core);
}

// Raw core with shared contexts ordered as Nat n, Nat m, Nat k:
// implies (Nat n) (implies (Nat m) (implies (Nat k) (implies IH_eq GOAL_eq)))
function proveMulDistrRightCore() : Thm {
    const ihEq = "equals (mul n (add m k)) (add (mul n m) (mul n k))";
    const lhs = "mul n (add m (succ k))";
    const mid1 = "mul n (succ (add m k))";
    const mid2 = "add (mul n (add m k)) n";
    const mid3 = "add (add (mul n m) (mul n k)) n";
    const mid4 = "add (mul n m) (add (mul n k) n)";
    const goalRhs = "add (mul n m) (mul n (succ k))";

    // E1: rewrite add m (succ k) to succ (add m k), then unfold mul on the right argument.
    const e1a0 = conditionalCongr(
        subst(S("n", "m", "m", "k"), thm("add-succ-right")),
        "t. mul n t",
    );
    const e1a1 = weaken(e1a0, "Nat k");
    const e1a2 = impliesExchange(e1a1);
    const e1a = weaken(e1a2, "Nat n");

    const natAddMK0 = subst(S("n", "m", "m", "k"), thm("Nat-add"));
    const natAddMK = weaken(natAddMK0, "Nat n");

    const e1b0 = subst(S("m", "add m k"), thm("mul-succ"));
    const e1b1 = weaken(e1b0, "Nat k");
    const e1b2 = impliesExchange(e1b1);
    const e1b3 = weaken(e1b2, "Nat m");
    const e1b4 = impliesExchange(e1b3);
    const e1b = conditionalModusPonens3(e1b4, natAddMK);

    const e1 = chainEq3(e1a, e1b);

    // E2: apply the induction hypothesis under add _ n.
    const e2raw = conditionalModusPonens(
        subst(S("x", "mul n (add m k)", "y", "add (mul n m) (mul n k)",
              "A", `t. equals (add (mul n (add m k)) n) (add t n)`),
            thm("equals_subst")),
        weaken(equalsRefl("add (mul n (add m k)) n"), ihEq),
    );
    const e2bridge0 = impliesTrans(
        e2raw,
        subst(S("x", mid2, "y", mid3,
              "A", `t. equals (${lhs}) t`),
            thm("equals_subst")),
    );
    const e2bridge = weaken(weaken(weaken(e2bridge0, "Nat k"), "Nat m"), "Nat n");
    const e12 = chainStaticImp3(e1, e2bridge);

    // E3: reassociate the final addition to isolate mul n (succ k).
    const assoc0 = subst(S("n", "mul n m", "m", "mul n k", "k", "n"), thm("add-assoc"));
    const assoc1 = innerExchange(assoc0);
    const assoc2 = impliesExchange(assoc1);
    const assoc3 = conditionalImpliesTrans(thm("Nat-mul"), assoc2);
    const natMulNK0 = subst(S("m", "k"), thm("Nat-mul"));
    const natMulNK1 = weaken(natMulNK0, "Nat m");
    const natMulNK2 = impliesExchange(natMulNK1);
    const assoc4 = weaken(assoc3, "Nat k");
    const assoc5 = impliesExchange(assoc4);
    const assoc6 = innerExchange(assoc5);
    const assoc = conditionalModusPonens3(assoc6, natMulNK2);

    const mulSucc0 = subst(S("m", "k"), thm("mul-succ"));
    const mulSuccSymRule0 = subst(
        S("x", "mul n (succ k)", "y", "add (mul n k) n"),
        thm("equals_sym"),
    );
    const mulSuccSymRule1 = weaken(mulSuccSymRule0, "Nat n");
    const mulSuccSym0 = conditionalModusPonens(
        liftRewriter(mulSuccSymRule1, "Nat k"),
        mulSucc0,
    );
    const mulSuccCongr0 = conditionalModusPonens(
        subst(S("x", "add (mul n k) n", "y", "mul n (succ k)",
              "A", "t. equals (add (mul n m) (add (mul n k) n)) (add (mul n m) t)"),
            thm("equals_subst")),
        weaken(equalsRefl("add (mul n m) (add (mul n k) n)"), "equals (add (mul n k) n) (mul n (succ k))"),
    );
    const mulSuccSym1 = conditionalModusPonens(
        liftRewriter(weaken(mulSuccCongr0, "Nat n"), "Nat k"),
        mulSuccSym0,
    );
    const mulSuccSym2 = weaken(mulSuccSym1, "Nat m");
    const mulSuccSym = impliesExchange(mulSuccSym2);

    const finalEq = chainEq3(assoc, mulSuccSym);
    const finalBridge0 = impliesExchange(subst(
        S("x", mid3, "y", goalRhs,
          "A", `t. equals (${lhs}) t`),
        thm("equals_subst"),
    ));
    const finalBridge1 = weaken(weaken(weaken(finalBridge0, "Nat k"), "Nat m"), "Nat n");
    const finalBridge = chainStaticImp3(finalEq, finalBridge1);

    return chainImp3(e12, finalBridge);
}

// implies (Nat n) (implies (Nat m) (implies (Nat k) (equals (mul (mul n m) k) (mul n (mul m k)))))
function proveMulAssoc() : Thm {
    const byK = inductNat(
        "k. implies (Nat x) (implies (Nat m) (equals (mul (mul x m) k) (mul x (mul m k))))",
        subst(S("n", "x", "k", "n"), proveMulAssocStep()),
        subst(S("n", "x"), proveMulAssocBase()),
    );
    return subst(S("x", "n", "n", "k"), innerExchange(impliesExchange(byK)));
}

// Base: implies (Nat n) (implies (Nat m) (equals (mul (mul n m) zero) (mul n (mul m zero))))
function proveMulAssocBase() : Thm {
    const left0 = subst(S("n", "mul n m"), thm("mul-zero"));
    const left1 = weaken(left0, "Nat n");
    const left = conditionalModusPonens(
        liftRewriter(left1, "Nat m"),
        thm("Nat-mul"),
    );

    const innerZero0 = subst(S("n", "m"), thm("mul-zero"));
    const innerCongr = weaken(conditionalCongr(innerZero0, "t. mul n t"), "Nat n");
    const outerZero = impliesExchange(weaken(thm("mul-zero"), "Nat m"));
    const right = chainEqNM(innerCongr, outerZero);

    const rightSym0 = subst(S("x", "mul n (mul m zero)", "y", "zero"), thm("equals_sym"));
    const rightSym = conditionalModusPonens(
        liftRewriter(weaken(rightSym0, "Nat n"), "Nat m"),
        right,
    );
    return chainEqNM(left, rightSym);
}

// Informal induction idea for mul-assoc.
//
// Again it is cleaner to induct on k:
//
// Base:
//   mul (mul n m) zero = zero = mul n (mul m zero).
//
// Step:
//   mul (mul n m) (succ k)
//   = add (mul (mul n m) k) (mul n m)                 [mul-succ]
//   = add (mul n (mul m k)) (mul n m)                 [IH]
//   = mul n (add (mul m k) m)                         [mul-distr-right]
//   = mul n (mul m (succ k)).                         [mul-succ]
function proveMulAssocStep() : Thm {
    const core = impliesExchange(innerExchange(proveMulAssocCore()));
    return packageStepOver2Hyps(core);
}

// Raw core with shared contexts ordered as Nat n, Nat m, Nat k:
// implies (Nat n) (implies (Nat m) (implies (Nat k) (implies IH_eq GOAL_eq)))
function proveMulAssocCore() : Thm {
    const ihEq = "equals (mul (mul n m) k) (mul n (mul m k))";
    const lhs = "mul (mul n m) (succ k)";
    const mid1 = "add (mul (mul n m) k) (mul n m)";
    const mid2 = "add (mul n (mul m k)) (mul n m)";
    const mid3 = "mul n (add (mul m k) m)";
    const goal = "mul n (mul m (succ k))";

    // E1: expand the left-hand side with mul-succ.
    const e10 = subst(S("n", "mul n m", "m", "k"), thm("mul-succ"));
    const e11 = impliesExchange(e10);
    const e12 = weaken(e11, "Nat m");
    const e13 = impliesExchange(e12);
    const e14 = weaken(e13, "Nat n");
    const e15 = innerExchange(e14);

    const natMulNM0 = weaken(thm("Nat-mul"), "Nat k");
    const natMulNM1 = impliesExchange(natMulNM0);
    const natMulNM = innerExchange(natMulNM1);
    const e1 = conditionalModusPonens3(e15, natMulNM);

    // E2: rewrite the recursive occurrence using the induction hypothesis.
    const e2raw = conditionalModusPonens(
        subst(S("x", "mul (mul n m) k", "y", "mul n (mul m k)",
              "A", "t. equals (add (mul (mul n m) k) (mul n m)) (add t (mul n m))"),
            thm("equals_subst")),
        weaken(equalsRefl("add (mul (mul n m) k) (mul n m)"), ihEq),
    );
    const e2bridge0 = impliesTrans(
        e2raw,
        subst(S("x", mid1, "y", mid2,
              "A", `t. equals (${lhs}) t`),
            thm("equals_subst")),
    );
    const e2bridge = weaken(weaken(weaken(e2bridge0, "Nat k"), "Nat m"), "Nat n");
    const e12ih = chainStaticImp3(e1, e2bridge);

    // E3: use right distributivity in reverse.
    const natMulMK0 = subst(S("n", "m", "m", "k"), thm("Nat-mul"));
    const natMulMK = weaken(natMulMK0, "Nat n");

    const distr0 = subst(S("m", "mul m k", "k", "m"), thm("mul-distr-right"));
    const distr1 = innerExchange(distr0);
    const distr2 = weaken(distr1, "Nat k");
    const distr3 = impliesExchange(distr2);
    const distr4 = innerExchange(distr3);
    const distr5 = conditionalModusPonens3(distr4, natMulMK);
    const distrSym0 = subst(S("x", mid3, "y", mid2), thm("equals_sym"));
    const distrSym1 = weaken(weaken(weaken(distrSym0, "Nat k"), "Nat m"), "Nat n");
    const distrSym = conditionalModusPonens3(distrSym1, distr5);

    // E4: fold mul m (succ k) back on the right.
    const ms0 = subst(S("n", "m", "m", "k"), thm("mul-succ"));
    const msCongRule0 = conditionalModusPonens(
        subst(S("x", "mul m (succ k)", "y", "add (mul m k) m",
              "A", "t. equals (mul n (mul m (succ k))) (mul n t)"),
            thm("equals_subst")),
        weaken(equalsRefl("mul n (mul m (succ k))"), "equals (mul m (succ k)) (add (mul m k) m)"),
    );
    const msCong0 = conditionalModusPonens(
        liftRewriter(weaken(msCongRule0, "Nat m"), "Nat k"),
        ms0,
    );
    const msSym0 = subst(S("x", goal, "y", mid3), thm("equals_sym"));
    const msSym1 = weaken(msSym0, "Nat m");
    const msSym2 = conditionalModusPonens(
        liftRewriter(msSym1, "Nat k"),
        msCong0,
    );
    const msSym = weaken(msSym2, "Nat n");

    const finalEq = chainEq3(distrSym, msSym);
    const finalBridge0 = impliesExchange(subst(
        S("x", mid2, "y", goal,
          "A", `t. equals (${lhs}) t`),
        thm("equals_subst"),
    ));
    const finalBridge1 = weaken(weaken(weaken(finalBridge0, "Nat k"), "Nat m"), "Nat n");
    const finalBridge = chainStaticImp3(finalEq, finalBridge1);

    return chainImp3(e12ih, finalBridge);
}

// implies (Nat n) (implies (Nat m) (Nat (mul n m)))
function proveNatMul() : Thm {
    const base = proveNatMulBase();
    const step = proveNatMulStep();
    return inductNat("n. implies (Nat m) (Nat (mul n m))", step, base);
}

// Base: implies (Nat m) (Nat (mul zero m))
function proveNatMulBase() : Thm {
    const mulZeroEq = equalsTrans(
        subst(S("n", "zero"), thm("mul_def")),
        subst(S("g", "zero", "h", "i u. add u m"), thm("primrec-zero")));
    // mulZeroEq: equals (mul zero m) zero
    const rewriter = subst(S("A", "t. Nat t"), substEquals(equalsSym(mulZeroEq)));
    // rewriter: implies (Nat zero) (Nat (mul zero m))
    const base = modusPonens(rewriter, thm("Nat-zero"));
    return weaken(base, "Nat m");
}

// Step: implies (Nat n) (implies IH (implies (Nat m) (Nat (mul (succ n) m))))
function proveNatMulStep() : Thm {
    // natN_to_rewrite: implies (Nat n) (implies (Nat (add (mul n m) m)) (Nat (mul (succ n) m)))
    const mulSL_sym = impliesTrans(mulSuccLeft(),
        subst(S("x", "mul (succ n) m", "y", "add (mul n m) m"), thm("equals_sym")));
    const eqSubstNat = subst(S("x", "add (mul n m) m", "y", "mul (succ n) m", "A", "t. Nat t"),
        thm("equals_subst"));
    const natN_to_rewrite = impliesTrans(mulSL_sym, eqSubstNat);

    // natAddMulInst: implies (Nat (mul n m)) (implies (Nat m) (Nat (add (mul n m) m)))
    const natAddMulInst = subst(S("n", "mul n m"), thm("Nat-add"));

    // Exchange and chain
    const exchAdd = impliesExchange(natAddMulInst);
    // exchAdd: implies (Nat m) (implies (Nat (mul n m)) (Nat (add (mul n m) m)))
    const natN_exch = impliesExchange(natN_to_rewrite);
    // natN_exch: implies (Nat (add (mul n m) m)) (implies (Nat n) (Nat (mul (succ n) m)))
    const hBC = weaken(natN_exch, "Nat m");
    const combined = conditionalImpliesTrans(exchAdd, hBC);
    // combined: implies (Nat m) (implies (Nat (mul n m)) (implies (Nat n) (Nat (mul (succ n) m))))
    const step3 = innerExchange(combined);
    // step3: implies (Nat m) (implies (Nat n) (implies (Nat (mul n m)) (Nat (mul (succ n) m))))
    const step4 = impliesExchange(step3);
    // step4: implies (Nat n) (implies (Nat m) (implies (Nat (mul n m)) (Nat (mul (succ n) m))))

    // S combinator to fold IH through Nat m
    const s_inst = subst(
        S("A", "Nat m", "B", "Nat (mul n m)", "C", "Nat (mul (succ n) m)"),
        thm("implies_2"));
    return impliesTrans(step4, s_inst);
}

// implies (Nat n) (implies (Nat m) (equals (mul n (succ m)) (add (mul n m) n)))
function proveMulSucc() : Thm {
    const base = proveMulSuccBase();
    const step = proveMulSuccStep();
    return inductNat("n. implies (Nat m) (equals (mul n (succ m)) (add (mul n m) n))", step, base);
}

// Base: implies (Nat m) (equals (mul zero (succ m)) (add (mul zero m) zero))
function proveMulSuccBase() : Thm {
    // mul zero (succ m) = 0: mul_def + primrec-zero
    const lhs = equalsTrans(
        subst(S("n", "zero", "m", "succ m"), thm("mul_def")),
        subst(S("g", "zero", "h", "i u. add u (succ m)"), thm("primrec-zero")));
    // add (mul zero m) zero = add 0 zero = 0: congr(mul zero m = 0) + add-zero
    const mulZeroM = equalsTrans(
        subst(S("n", "zero"), thm("mul_def")),
        subst(S("g", "zero", "h", "i u. add u m"), thm("primrec-zero")));
    const rhs = equalsTrans(
        congr(mulZeroM, "t. add t zero"),
        subst(S("n", "zero"), thm("add-zero")));
    return weaken(equalsTrans(lhs, equalsSym(rhs)), "Nat m");
}

// Informal induction idea for mul-succ.
//
// We induct on n. The base case is immediate because both sides reduce to zero.
//
// For the step, assume the induction hypothesis
//   IH: mul n (succ m) = add (mul n m) n.
// Then expand the left-hand side once using recursion on the first argument:
//   mul (succ n) (succ m)
//   = add (mul n (succ m)) (succ m).
// Rewrite the inner multiplication with IH:
//   = add (add (mul n m) n) (succ m).
// Now perform the standard arithmetic rearrangement:
//   = add (add (mul n m) m) (succ n).
// Finally fold multiplication back on the first argument:
//   = add (mul (succ n) m) (succ n).
//
// The proof sketch below makes E1/E2/E8 explicit. The hard part is the middle
// rearrangement, where we repeatedly reassociate, commute, and transport
// equalities through the shared assumptions Nat n and Nat m. That is the point
// where a more reusable proof tool would help.
//
// Step: implies (Nat n) (implies IH (implies (Nat m) (equals (mul (succ n) (succ m)) (add (mul (succ n) m) (succ n)))))
function proveMulSuccStep() : Thm {
    // We chain equalities:
    // E1: mul (succ n) (succ m) = add (mul n (succ m)) (succ m)      [mulSuccLeft, m:=succ m]
    // E2: add (mul n (succ m)) (succ m) = add (add (mul n m) n) (succ m)  [IH under congr]
    // E3: add (add (mul n m) n) (succ m) = succ (add (add (mul n m) n) m)  [add-succ-right]
    // E4: succ (add (add (mul n m) n) m) = succ (add (mul n m) (add n m))  [add-assoc]
    // E5: succ (add (mul n m) (add n m)) = succ (add (mul n m) (add m n))  [add-comm]
    // E6: succ (add (mul n m) (add m n)) = succ (add (add (mul n m) m) n)  [add-assoc sym]
    // E7: succ (add (add (mul n m) m) n) = add (add (mul n m) m) (succ n)  [add-succ-right sym]
    // E8: add (add (mul n m) m) (succ n) = add (mul (succ n) m) (succ n)   [mulSuccLeft sym]

    // Build the chain under conditions (Nat n, Nat m, IH)
    // Use proveMulSuccCore to build the main equality chain
    const core = proveMulSuccCore();
    // core: implies (Nat n) (implies (Nat m) (implies IH_eq (equals (mul (succ n) (succ m)) (add (mul (succ n) m) (succ n)))))
    // where IH_eq = equals (mul n (succ m)) (add (mul n m) n)

    // Lift through Nat m using S combinator to convert inner IH_eq to outer IH
    const [_natn, inner1] = destImplies(conclOf(core));
    const [_natm, inner2] = destImplies(inner1);
    const [ih_eq, _goal_eq] = destImplies(inner2);

    // K+S lift: from implies (Nat m) (implies IH_eq GOAL_eq)
    //           to implies (implies (Nat m) IH_eq) (implies (Nat m) GOAL_eq)
    const s_m = subst(S("A", "Nat m", "B", ih_eq, "C",
        "equals (mul (succ n) (succ m)) (add (mul (succ n) m) (succ n))"), thm("implies_2"));
    return impliesTrans(core, s_m);
}

// Core: implies (Nat n) (implies (Nat m) (implies IH_eq GOAL_eq))
function proveMulSuccCore() : Thm {
    // E1: implies (Nat n) (equals (mul (succ n) (succ m)) (add (mul n (succ m)) (succ m)))
    const e1 = subst(S("m", "succ m"), mulSuccLeft());

    // E2 bridge: implies IH_eq (equals (add (mul n (succ m)) (succ m)) (add (add (mul n m) n) (succ m)))
    // IH_eq = equals (mul n (succ m)) (add (mul n m) n)
    const e2 = conditionalModusPonens(
        subst(S("x", "mul n (succ m)", "y", "add (mul n m) n",
              "A", "t. equals (add (mul n (succ m)) (succ m)) (add t (succ m))"),
            thm("equals_subst")),
        weaken(equalsRefl("add (mul n (succ m)) (succ m)"),
            "equals (mul n (succ m)) (add (mul n m) n)"));

    const bridge12 = subst(
        S("x", "add (mul n (succ m)) (succ m)", "y", "add (add (mul n m) n) (succ m)",
          "A", "t. equals (mul (succ n) (succ m)) t"), thm("equals_subst"));
    const e2to = impliesTrans(e2, bridge12);
    const e2x = impliesExchange(e2to);

    // Chain E1+E2: implies (Nat n) (implies IH_eq (equals (mul (succ n) (succ m)) (add (add (mul n m) n) (succ m))))
    const e12 = conditionalModusPonens(weaken(e2x, "Nat n"), e1);

    // E3-E7: the middle rearrangement chain
    // Build: implies (Nat n) (implies (Nat m) (equals (add (add (mul n m) n) (succ m)) (add (add (mul n m) m) (succ n))))
    const mid = proveMulSuccMid();

    // E8: implies (Nat n) (equals (add (add (mul n m) m) (succ n)) (add (mul (succ n) m) (succ n)))
    const e8_eq = impliesTrans(mulSuccLeft(),
        subst(S("x", "mul (succ n) m", "y", "add (mul n m) m"), thm("equals_sym")));
    const e8 = conditionalCongr(e8_eq, "t. add t (succ n)");

    // Chain mid+E8: implies (Nat n) (implies (Nat m) (equals (add (add (mul n m) n) (succ m)) (add (mul (succ n) m) (succ n))))
    const mid_e8_bridge = impliesTrans(e8,
        subst(S("x", "add (add (mul n m) m) (succ n)", "y", "add (mul (succ n) m) (succ n)",
              "A", "t. equals (add (add (mul n m) n) (succ m)) t"), thm("equals_subst")));
    const mid_e8_lifted = liftRewriter(mid_e8_bridge, "Nat m");
    const mid_e8 = conditionalModusPonens(mid_e8_lifted, mid);

    // Chain E12 + mid_e8 under the shared outer conditions Nat n and Nat m
    const final_bridge0 = subst(
        S("x", "add (add (mul n m) n) (succ m)", "y", "add (mul (succ n) m) (succ n)",
          "A", "t. equals (mul (succ n) (succ m)) t"), thm("equals_subst"));
    const final_bridge = modusPonens(
        liftFormulaThrough(liftFormulaThrough(final_bridge0, "Nat m"), "Nat n"),
        mid_e8);
    const e12nm = impliesExchange(weaken(e12, "Nat m"));
    return chainImp2(e12nm, final_bridge);
}

// Helper: lift pure formula (implies X Y) through condition C
// Returns: implies (implies C X) (implies C Y)
function liftFormulaThrough(formula: Thm, c: string | Term) : Thm {
    const [x, y] = destImplies(conclOf(formula));
    const k = subst(S("A", conclOf(formula), "B", c), thm("implies_1"));
    const s = subst(S("A", c, "B", x, "C", y), thm("implies_2"));
    return modusPonens(impliesTrans(k, s), formula);
}

// Discharge a third condition using S combinator:
// Given th: H1 → H2 → (H3 → C) and prem: H1 → H2 → H3
// Returns: H1 → H2 → C
function dischargeInner(th: Thm, prem: Thm) : Thm {
    const [_h1, inner1] = destImplies(conclOf(th));
    const [h2, inner2] = destImplies(inner1);
    const [h3, c] = destImplies(inner2);
    const s = subst(S("A", h2, "B", h3, "C", c), thm("implies_2"));
    // s: (H2 → H3 → C) → (H2 → H3) → (H2 → C)
    const step = impliesTrans(th, s);
    // step: H1 → (H2 → H3) → (H2 → C)
    return conditionalModusPonens(step, prem);
}

// Chain two doubly-conditional implications:
// ab: H1 -> H2 -> (A -> B)
// bc: H1 -> H2 -> (B -> C)
// Returns: H1 -> H2 -> (A -> C)
function chainImp2(ab: Thm, bc: Thm) : Thm {
    const [h1, innerAB1] = destImplies(conclOf(ab));
    const [h2, abBody] = destImplies(innerAB1);
    const [a, b] = destImplies(abBody);
    const [_, innerBC1] = destImplies(conclOf(bc));
    const [__, bcBody] = destImplies(innerBC1);
    const [_b, c] = destImplies(bcBody);
    const H1 = tyAtom("H1");
    const H2 = tyAtom("H2");
    const A = tyAtom("A");
    const B = tyAtom("B");
    const C = tyAtom("C");
    const AB = tyImp(H1, tyImp(H2, tyImp(A, B)));
    const BC = tyImp(H1, tyImp(H2, tyImp(B, C)));
    const rule = provePureImplication(
        tyImp(AB, tyImp(BC, tyImp(H1, tyImp(H2, tyImp(A, C))))),
        lam("ab", AB, lam("bc", BC, lam("h1", H1, lam("h2", H2, lam("a", A,
            app(
                app(app(v("bc"), v("h1")), v("h2")),
                app(app(app(v("ab"), v("h1")), v("h2")), v("a")),
            ),
        ))))),
    );
    const inst = subst(S("H1", h1, "H2", h2, "A", a, "B", b, "C", c), rule);
    return modusPonens(modusPonens(inst, ab), bc);
}

// Apply a binary implication rule under three shared hypotheses.
// rule: A -> B -> C
// left: H1 -> H2 -> H3 -> A
// right: H1 -> H2 -> H3 -> B
// returns: H1 -> H2 -> H3 -> C
function applyBinaryRule3(rule: Thm, left: Thm, right: Thm) : Thm {
    const [a, bc] = destImplies(conclOf(rule));
    const [b, c] = destImplies(bc);

    const [h1, left1] = destImplies(conclOf(left));
    const [h2, left2] = destImplies(left1);
    const [h3, _leftBody] = destImplies(left2);

    const H1 = tyAtom("H1");
    const H2 = tyAtom("H2");
    const H3 = tyAtom("H3");
    const A = tyAtom("A");
    const B = tyAtom("B");
    const C = tyAtom("C");
    const ruleTy = tyImp(A, tyImp(B, C));
    const leftTy = tyImp(H1, tyImp(H2, tyImp(H3, A)));
    const rightTy = tyImp(H1, tyImp(H2, tyImp(H3, B)));

    const applicator = provePureImplication(
        tyImp(ruleTy, tyImp(leftTy, tyImp(rightTy, tyImp(H1, tyImp(H2, tyImp(H3, C)))))),
        lam("rule", ruleTy, lam("left", leftTy, lam("right", rightTy, lam("h1", H1, lam("h2", H2, lam("h3", H3,
            app(
                app(v("rule"),
                    app(app(app(v("left"), v("h1")), v("h2")), v("h3")),
                ),
                app(app(app(v("right"), v("h1")), v("h2")), v("h3")),
            ),
        )))))),
    );
    const inst = subst(S("H1", h1, "H2", h2, "H3", h3, "A", a, "B", b, "C", c), applicator);
    return modusPonens(modusPonens(modusPonens(inst, rule), left), right);
}

// Given imp: H1 -> H2 -> H3 -> (A -> B)
// and   assm: H1 -> H2 -> H3 -> A
// return    H1 -> H2 -> H3 -> B
function conditionalModusPonens3(implication: Thm, assumption: Thm) : Thm {
    const [_h1, inner1] = destImplies(conclOf(implication));
    const [_h2, inner2] = destImplies(inner1);
    const [_h3, ab] = destImplies(inner2);
    const [a, b] = destImplies(ab);

    const A = tyAtom("A");
    const B = tyAtom("B");
    const rule = subst(
        S("A", a, "B", b),
        provePureImplication(
            tyImp(tyImp(A, B), tyImp(A, B)),
            lam("f", tyImp(A, B), lam("a", A, app(v("f"), v("a")))),
        ),
    );
    return applyBinaryRule3(rule, implication, assumption);
}

// Chain under three shared hypotheses:
// ab: H1 -> H2 -> H3 -> (A -> B)
// bc: H1 -> H2 -> H3 -> (B -> C)
// returns: H1 -> H2 -> H3 -> (A -> C)
function chainImp3(ab: Thm, bc: Thm) : Thm {
    const [_, innerAB1] = destImplies(conclOf(ab));
    const [__, innerAB2] = destImplies(innerAB1);
    const [___, abBody] = destImplies(innerAB2);
    const [a, b] = destImplies(abBody);

    const [____, innerBC1] = destImplies(conclOf(bc));
    const [_____, innerBC2] = destImplies(innerBC1);
    const [______, bcBody] = destImplies(innerBC2);
    const [_b, c] = destImplies(bcBody);

    const A = tyAtom("A");
    const B = tyAtom("B");
    const C = tyAtom("C");
    const rule = subst(
        S("A", a, "B", b, "C", c),
        provePureImplication(
            tyImp(tyImp(A, B), tyImp(tyImp(B, C), tyImp(A, C))),
            lam("ab", tyImp(A, B), lam("bc", tyImp(B, C), lam("a", A,
                app(v("bc"), app(v("ab"), v("a"))),
            ))),
        ),
    );
    return applyBinaryRule3(rule, ab, bc);
}

// Combine a static equality with a contextual rewriter under three shared hypotheses:
// left:  H1 -> H2 -> H3 -> B
// right: H1 -> H2 -> H3 -> (A -> (B -> C))
// returns: H1 -> H2 -> H3 -> (A -> C)
function chainStaticImp3(left: Thm, right: Thm) : Thm {
    const [_, left1] = destImplies(conclOf(left));
    const [__, left2] = destImplies(left1);
    const [___, b] = destImplies(left2);

    const [____, right1] = destImplies(conclOf(right));
    const [_____, right2] = destImplies(right1);
    const [______, rightBody] = destImplies(right2);
    const [a, bc] = destImplies(rightBody);
    const [_b, c] = destImplies(bc);

    const A = tyAtom("A");
    const B = tyAtom("B");
    const C = tyAtom("C");
    const rule = subst(
        S("A", a, "B", b, "C", c),
        provePureImplication(
            tyImp(B, tyImp(tyImp(A, tyImp(B, C)), tyImp(A, C))),
            lam("b", B, lam("r", tyImp(A, tyImp(B, C)), lam("a", A,
                app(app(v("r"), v("a")), v("b")),
            ))),
        ),
    );
    return applyBinaryRule3(rule, left, right);
}

// Chain equalities under three shared hypotheses.
// eq_ab: H1 -> H2 -> H3 -> equals a b
// eq_bc: H1 -> H2 -> H3 -> equals b c
// returns: H1 -> H2 -> H3 -> equals a c
function chainEq3(eq_ab: Thm, eq_bc: Thm) : Thm {
    const [_, innerAB1] = destImplies(conclOf(eq_ab));
    const [__, innerAB2] = destImplies(innerAB1);
    const [___, eqAB] = destImplies(innerAB2);
    const [a, b] = destEquals(eqAB);

    const [____, innerBC1] = destImplies(conclOf(eq_bc));
    const [_____, innerBC2] = destImplies(innerBC1);
    const [______, eqBC] = destImplies(innerBC2);
    const [_b, c] = destEquals(eqBC);

    const transGen = subst(S("A", "t. equals A t"), thm("equals_subst"));
    const bridge = subst(S("A", a, "x", b, "y", c), transGen);
    const exBridge = impliesExchange(bridge);
    return applyBinaryRule3(exBridge, eq_ab, eq_bc);
}

// Repackage a raw induction core:
// core: H1 -> H2 -> H3 -> (A -> B)
// into  H1 -> (H2 -> H3 -> A) -> (H2 -> H3 -> B)
function packageStepOver2Hyps(core: Thm) : Thm {
    const [h1, inner1] = destImplies(conclOf(core));
    const [h2, inner2] = destImplies(inner1);
    const [h3, ab] = destImplies(inner2);
    const [a, b] = destImplies(ab);

    const H1 = tyAtom("H1");
    const H2 = tyAtom("H2");
    const H3 = tyAtom("H3");
    const A = tyAtom("A");
    const B = tyAtom("B");
    const coreTy = tyImp(H1, tyImp(H2, tyImp(H3, tyImp(A, B))));
    const ihTy = tyImp(H2, tyImp(H3, A));
    const goalTy = tyImp(H2, tyImp(H3, B));

    const packer = provePureImplication(
        tyImp(coreTy, tyImp(H1, tyImp(ihTy, goalTy))),
        lam("core", coreTy, lam("h1", H1, lam("ih", ihTy, lam("h2", H2, lam("h3", H3,
            app(
                app(app(app(v("core"), v("h1")), v("h2")), v("h3")),
                app(app(v("ih"), v("h2")), v("h3")),
            ),
        ))))),
    );
    const inst = subst(S("H1", h1, "H2", h2, "H3", h3, "A", a, "B", b), packer);
    return modusPonens(inst, core);
}

// Chain two doubly-conditional equalities:
// eq_ab: H1 → H2 → equals a b
// eq_bc: H1 → H2 → equals b c
// Returns: H1 → H2 → equals a c
function chainEqNM(eq_ab: Thm, eq_bc: Thm) : Thm {
    const [_, inner_ab] = destImplies(conclOf(eq_ab));
    const [__, eq_ab_body] = destImplies(inner_ab);
    const [a, b] = destEquals(eq_ab_body);
    const [___, inner_bc] = destImplies(conclOf(eq_bc));
    const [____, eq_bc_body] = destImplies(inner_bc);
    const [_b, c] = destEquals(eq_bc_body);

    // General transitivity: implies (equals x y) (implies (equals A x) (equals A y))
    const transGen = subst(S("A", "t. equals A t"), thm("equals_subst"));
    // Instantiate: implies (equals b c) (implies (equals a b) (equals a c))
    const bridge = subst(S("A", a, "x", b, "y", c), transGen);
    // Exchange: (equals a b) → (equals b c) → (equals a c)
    const ex_bridge = impliesExchange(bridge);

    // Lift through H2 then H1
    const [h1, _inner] = destImplies(conclOf(eq_ab));
    const [h2, _body] = destImplies(_inner);
    const lifted = liftFormulaThrough(liftFormulaThrough(ex_bridge, h2), h1);
    // lifted: (H1 → H2 → equals a b) → (H1 → H2 → (equals b c → equals a c))
    const step1 = modusPonens(lifted, eq_ab);
    // step1: H1 → H2 → (equals b c → equals a c)
    // = H1 → (H2 → (X → Z))

    // S combinator at H2 level to fold eq_bc
    const [_h1b, s1_inner] = destImplies(conclOf(step1));
    const [_h2b, s1_inner2] = destImplies(s1_inner);
    const [x_t, z_t] = destImplies(s1_inner2);
    const s_inst = subst(S("A", h2, "B", x_t, "C", z_t), thm("implies_2"));
    const step2 = impliesTrans(step1, s_inst);
    // step2: H1 → (H2 → X) → (H2 → Z)
    return conditionalModusPonens(step2, eq_bc);
}

// E3-E7: implies (Nat n) (implies (Nat m) (equals (add (add (mul n m) n) (succ m)) (add (add (mul n m) m) (succ n))))
function proveMulSuccMid() : Thm {
    // This part does check, but it is a good example of the kind of boilerplate
    // we should eventually absorb into reusable proof tools.

    // --- Derive Nat closures ---
    // natAddXY: Nat n → Nat m → Nat(add (mul n m) n)
    const natAddXY_ex = impliesExchange(subst(S("n", "mul n m", "m", "n"), thm("Nat-add")));
    // natAddXY_ex: Nat n → Nat(mul n m) → Nat(add (mul n m) n)
    const natAddXY = conditionalImpliesTrans(thm("Nat-mul"), natAddXY_ex);

    // natAddXZ: Nat n → Nat m → Nat(add (mul n m) m)
    const natAddXZ_ex = impliesExchange(subst(S("n", "mul n m"), thm("Nat-add")));
    // natAddXZ_ex: Nat m → Nat(mul n m) → Nat(add (mul n m) m)
    const natAddXZ_s = subst(S("A", "Nat m", "B", "Nat (mul n m)", "C", "Nat (add (mul n m) m)"), thm("implies_2"));
    const natAddXZ_step = modusPonens(natAddXZ_s, natAddXZ_ex);
    const natAddXZ = impliesTrans(thm("Nat-mul"), natAddXZ_step);

    // --- Build P1: add-assoc[n:=mul n m, m:=n, k:=m] ---
    // Raw: Nat(mul n m) → Nat n → Nat m → equals (add (add (mul n m) n) m) (add (mul n m) (add n m))
    const p1_raw = subst(S("n", "mul n m", "m", "n", "k", "m"), thm("add-assoc"));
    // Reorder to Nat n → Nat m → Nat(mul n m) → equals ...
    const p1_r1 = impliesExchange(p1_raw);
    const p1_r2 = innerExchange(p1_r1);
    const p1 = dischargeInner(p1_r2, thm("Nat-mul"));

    // --- Build P2: add-comm congr ---
    // conditionalCongr only handles single-conditional equalities; add-comm is doubly-conditional.
    // Build congr formula manually: (equals (add n m) (add m n)) → (equals (add X (add n m)) (add X (add m n)))
    const p2_subst = subst(
        S("x", "add n m", "y", "add m n",
          "A", "t. equals (add (mul n m) (add n m)) (add (mul n m) t)"), thm("equals_subst"));
    const p2_congr = conditionalModusPonens(p2_subst,
        weaken(equalsRefl("add (mul n m) (add n m)"), "equals (add n m) (add m n)"));
    const p2 = impliesTrans(thm("add-comm"), liftFormulaThrough(p2_congr, "Nat m"));

    // --- Build P3: add-assoc sym ---
    // Raw: Nat(mul n m) → Nat m → Nat n → equals (add (add (mul n m) m) n) (add (mul n m) (add m n))
    const p3_raw = subst(S("n", "mul n m", "m", "m", "k", "n"), thm("add-assoc"));
    const p3_r1 = impliesExchange(p3_raw);
    const p3_r2 = innerExchange(p3_r1);
    const p3_r3 = impliesExchange(p3_r2);
    const p3_discharged = dischargeInner(p3_r3, thm("Nat-mul"));
    const p3_sym = subst(
        S("x", "add (add (mul n m) m) n", "y", "add (mul n m) (add m n)"), thm("equals_sym"));
    const p3 = impliesTrans(p3_discharged, liftFormulaThrough(p3_sym, "Nat m"));

    // --- Chain P1+P2+P3 ---
    const p12 = chainEqNM(p1, p2);
    const p123 = chainEqNM(p12, p3);

    // --- Wrap under succ ---
    const succSubst = subst(
        S("x", "add (add (mul n m) n) m", "y", "add (add (mul n m) m) n",
          "A", "t. equals (succ (add (add (mul n m) n) m)) (succ t)"), thm("equals_subst"));
    const succRefl = equalsRefl("succ (add (add (mul n m) n) m)");
    const succCongr = conditionalModusPonens(succSubst,
        weaken(succRefl, "equals (add (add (mul n m) n) m) (add (add (mul n m) m) n)"));
    const p123_succ = impliesTrans(p123, liftFormulaThrough(succCongr, "Nat m"));

    // --- E3: add-succ-right ---
    const e3_raw = subst(S("n", "add (mul n m) n"), thm("add-succ-right"));
    const e3 = conditionalImpliesTrans(natAddXY, weaken(e3_raw, "Nat n"));

    // --- E7: add-succ-right sym ---
    const e7_fwd = subst(S("n", "add (mul n m) m", "m", "n"), thm("add-succ-right"));
    const e7_sym_formula = subst(
        S("x", "add (add (mul n m) m) (succ n)", "y", "succ (add (add (mul n m) m) n)"), thm("equals_sym"));
    const e7_raw = impliesTrans(e7_fwd, e7_sym_formula);
    const e7 = conditionalImpliesTrans(natAddXZ, weaken(e7_raw, "Nat n"));

    // --- Chain all: e3 + p123_succ + e7 ---
    const chain1 = chainEqNM(e3, p123_succ);
    return chainEqNM(chain1, e7);
}
