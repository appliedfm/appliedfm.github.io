(*
 * Coq 8.13.2
 * https://github.com/jwiegley/category-theory
 *)

From Coq Require Import Setoid.

From Category Require Import Theory.

(* We will now define the category of Coq types & functions.
 * To do this, we need to define
 *   obj := Type
 *   hom X Y := X -> Y
 *   id X x := x
 *   compose g f x := g (f x)
 * The standard library defines these things for us, so there's very
 * little work for us to do.
 *)
Definition MyCoqCategory: Category.
Proof.
    unshelve refine (
        Build_Category'
            (@Basics.arrow)
            (@Datatypes.id)
            (@Basics.compose)
    ) ; intros; try reflexivity.
    1: refine {|
        Setoid.equiv := fun f g => forall x, f x = g x
    |} ; constructor.
    all: cbv ; congruence.
Defined.

Fail Definition foo: obj[MyCoqCategory]
 := obj[MyCoqCategory]
.

Print Functor.