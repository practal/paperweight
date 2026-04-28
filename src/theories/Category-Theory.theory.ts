import { beginTheory, declare, axiom, endTheory, includeTheory, conjecture } from "../workbench.js";
import "./Implication.theory.js";
import "./Equality.theory.js";

beginTheory();
includeTheory("Implication");
includeTheory("Equality");

// ============================================================
// PART 1: ONTOLOGY — Objects, Collections, and Undefinedness
// ============================================================
//
// In abstraction logic, every term denotes a value in a single
// mathematical universe. Values are classified by predicates:
//
//   object x     — x is an object (atom, urelement)
//   collection C — C is a collection (can have members)
//   elem x C     — x is a member of collection C
//
// Four kinds of values:
//   1. Both object and collection  (e.g., ℕ: a number and a set)
//   2. Object only                 (e.g., 42)
//   3. Collection only             (e.g., the class of all objects)
//   4. Neither — "undefined" / "error" values
//
// Undefinedness is natural in abstraction logic: operations like
// comp, ap, elem always produce a value. When inputs are ill-typed,
// results simply satisfy no useful predicate — no error handling,
// option types, or partial functions needed.

declare("object x");
declare("collection C");
declare("elem x C");

// Only collections can have members
axiom("elem-collection", "implies (elem x C) (collection C)");

// ============================================================
// PART 2: LEVEL HIERARCHY
// ============================================================
//
// Levels stratify the universe to handle size:
//   - Every object exists at some level
//   - Some collections have levels (e.g., ℕ at level 0)
//   - Some collections are too large for any level (e.g., the
//     class of ALL objects has no level)
//   - obj-col n (all level-n objects) is at level n+1
//
// This prevents Russell-style paradoxes within a single universe.

declare("Lev n");
declare("lev-zero");
declare("lev-succ n");
declare("at-lev x n");
declare("obj-col n");

// Level number formation
axiom("Lev-zero", "Lev lev-zero");
axiom("Lev-succ", "implies (Lev n) (Lev (lev-succ n))");

// obj-col n: the collection of all objects at level n
axiom("obj-col-is-collection", "implies (Lev n) (collection (obj-col n))");
axiom("obj-col-at-lev", "implies (Lev n) (at-lev (obj-col n) (lev-succ n))");
axiom("obj-col-intro",
    "implies (object x) (implies (at-lev x n) (elem x (obj-col n)))");
axiom("obj-col-elim-object", "implies (elem x (obj-col n)) (object x)");
axiom("obj-col-elim-lev", "implies (elem x (obj-col n)) (at-lev x n)");

// ============================================================
// PART 3: FUNCTIONS
// ============================================================
//
// Functions between collections. ap f x always produces a value —
// if x is outside the domain of f, the result is "undefined"
// (satisfies no predicate). This models partiality naturally.

declare("fun f A B");
declare("ap f x");

// A function maps domain elements to codomain elements
axiom("fun-ap",
    "implies (fun f A B) (implies (elem x A) (elem (ap f x) B))");

// ============================================================
// PART 4: CATEGORIES
// ============================================================
//
// A category has objects, morphisms, identities, and composition.
// comp C f g always produces a value — with non-composable f, g
// the result is "undefined" (satisfies no hom predicate).

declare("Cat C");
declare("cat-ob C x");
declare("hom C x y f");
declare("id-mor C x");
declare("comp C f g");

// Categories and their objects live in the universe
axiom("Cat-is-object", "implies (Cat C) (object C)");
axiom("cat-ob-is-object", "implies (cat-ob C x) (object x)");

// Identity morphism
axiom("hom-id",
    "implies (Cat C) (implies (cat-ob C x) (hom C x x (id-mor C x)))");

// Composition
axiom("hom-comp",
    "implies (hom C x y f) (implies (hom C y z g) (hom C x z (comp C f g)))");

// Identity laws
axiom("cat-id-left",
    "implies (hom C x y f) (equals (comp C (id-mor C x) f) f)");
axiom("cat-id-right",
    "implies (hom C x y f) (equals (comp C f (id-mor C y)) f)");

// Associativity
axiom("cat-assoc",
    "implies (hom C x y f) (implies (hom C y z g) (implies (hom C z w h) (equals (comp C (comp C f g) h) (comp C f (comp C g h)))))");

// ============================================================
// PART 5: THE CATEGORY SET
// ============================================================
//
// Set-cat n is the category of collections at level n.
// Morphisms are functions between collections.
// Set-cat n is itself an object at level n+1 — but not a
// collection (it is a category, not a container).

declare("Set-cat n");

axiom("Set-is-cat", "implies (Lev n) (Cat (Set-cat n))");
axiom("Set-at-lev", "implies (Lev n) (at-lev (Set-cat n) (lev-succ n))");
axiom("Set-ob",
    "implies (Lev n) (implies (collection A) (implies (at-lev A n) (cat-ob (Set-cat n) A)))");
axiom("Set-hom",
    "implies (Lev n) (implies (fun f A B) (implies (at-lev A n) (implies (at-lev B n) (hom (Set-cat n) A B f))))");

// ============================================================
// PART 6: FUNCTORS
// ============================================================

declare("Functor F C D");
declare("fobj F x");
declare("fmap F f");

// Functors preserve objects
axiom("functor-ob",
    "implies (Functor F C D) (implies (cat-ob C x) (cat-ob D (fobj F x)))");

// Functors preserve morphisms
axiom("functor-hom",
    "implies (Functor F C D) (implies (hom C x y f) (hom D (fobj F x) (fobj F y) (fmap F f)))");

// Functors preserve identity
axiom("functor-id",
    "implies (Functor F C D) (implies (cat-ob C x) (equals (fmap F (id-mor C x)) (id-mor D (fobj F x))))");

// Functors preserve composition
axiom("functor-comp",
    "implies (Functor F C D) (implies (hom C x y f) (implies (hom C y z g) (equals (fmap F (comp C f g)) (comp D (fmap F f) (fmap F g)))))");

// ============================================================
// CONJECTURES
// ============================================================

// Identity composed with itself is itself
conjecture("id-comp-self",
    "implies (Cat C) (implies (cat-ob C x) (equals (comp C (id-mor C x) (id-mor C x)) (id-mor C x)))",
    []);

// The collection of level-n objects is an object of Set at level n+1
conjecture("obj-col-in-Set",
    "implies (Lev n) (cat-ob (Set-cat (lev-succ n)) (obj-col n))",
    []);

// Set-cat n is an object in the universe
conjecture("Set-is-object",
    "implies (Lev n) (object (Set-cat n))",
    []);

// Functors map identity morphisms to morphisms
conjecture("functor-id-is-hom",
    "implies (Functor F C D) (implies (Cat C) (implies (cat-ob C x) (hom D (fobj F x) (fobj F x) (fmap F (id-mor C x)))))",
    []);

endTheory("Category-Theory");
