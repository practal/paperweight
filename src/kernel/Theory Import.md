# Theory Import

A theory hosts the following things:

* declarations of abstractions, in the form of a signature
* axioms, saved under a label
* definitions, saved under a label
* other theorems, saved under a label

Labels must be unique across axioms, definitions and theorems,
for example, you cannot have an axiom and a definition under the same label.

When importing a source theory S into a target theory T, we proceed
as described in the following.

## Importing Declarations

T receives all the declarations of S. If a declaration of S
overlaps with a declaration of T, they must be identical.

## Importing Axioms

To import an axiom s with label l of theory S into T, we first
check if the label l is already used in T. If not, we add
the axiom s with label l to T. Otherwise, let t be the theorem
corresponding to label l in T. If s and t are the same,
we do nothing. If s and t are different, the import fails.

## Importing Theorems

This works the same as importing axioms.
To import a theorem s with label l of theory S into T, we first
check if the label l is already used in T. If not, we add
the theorem s with label l to T. Otherwise, let t be the theorem
corresponding to label l in T. If s and t are the same,
we do nothing. If s and t are different, the import fails.

## Importing Definitions

To import a definition d with corresponding theorem s and label l,
we check if the label l is already used in T. If not, we need to make
sure that d does not overlap with any existing definition in T, unless
they are indeed the same definition (same relation, head, definiens and
corresponding rule). If there is no incompatible overlap,
we add definition d to theory T under label l. If there is one, the import fails.
If the label l is already used in T, the corresponding theorem t in T must be
identical to s, in which case we do nothing, otherwise the import fails. 

The correctness of theory import can be seen by recognizing 
that after import, all theorems will be associated with correct and 
grounded proofs. *Grounded* means here that a proof has no circles,
and that all of its leaves are axioms.
