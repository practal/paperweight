import { axiom, beginTheory, declare, endTheory, have, includeTheory, S, subst, Thm, thm, define } from "../workbench.js";
import "./Positive-Logic.theory.js";
import "./Equality.theory.js";
import { modusPonens, conditionalModusPonens, impliesTrans } from "./Implication.theory.js";

// Johansson's Minimal Propositional Logic (1937)
//
// This is intuitionistic propositional logic without the principle of explosion
// (ex falso quodlibet). Falsity is a primitive proposition, and negation is
// defined as implication to falsity, but false does NOT imply everything.
//
// Reference: I. Johansson, "Der Minimalkalkül, ein reduzierter
// intuitionistischer Formalismus", Compositio Mathematica 4, 1937.

beginTheory();
includeTheory("Positive-Logic");
includeTheory("Equality");
declare("false");
define("not A", "implies A false");
define("true", "not false");
define("equiv A B", "and (implies A B) (implies B A)");
endTheory("Minimal-Logic");
