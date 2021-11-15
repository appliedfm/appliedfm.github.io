Require Import Coq.ZArith.Zdiv.
Local Open Scope Z_scope.

Eval cbv in snd (fst (1, 2, 4)).


Structure Pointer: Type := {
    pointer_base: Z;
    pointer_offset: Z;
    pointer_offset__align: Zmod pointer_offset 8 = 0;
    pointer_offset__nonneg: 0 <= pointer_offset;
}.

Axiom my_ptr_base: Z.
Axiom my_ptr_offset: Z.

(* Using refine *)
Definition my_pointer: Pointer.
refine {|
    pointer_base := my_ptr_base;
    pointer_offset := my_ptr_offset;
    pointer_offset__align := _;
    pointer_offset__nonneg := _;
|}.
Proof.
  { (* Time to prove pointer_offset__align ... *) admit. }
  { (* Time to prove pointer_offset__nonneg ... *) admit. }
Admitted.

Definition pointer_base_is_zero (x: Pointer):
    bool
 := match x with
    | {| pointer_base := 0%Z |} => true
    | _ => false
    end.

Axiom my_other_ptr_base: Z.
Axiom my_other_ptr_offset: Z.

(* Using Program Definition *)
Program Definition my_other_pointer: Pointer := {|
    pointer_base := my_other_ptr_base;
    pointer_offset := my_other_ptr_offset;
|}.
Next Obligation.
    (* Time to prove pointer_offset__align ... *)
    admit.
Admitted.
Next Obligation.
    (* Time to prove pointer_offset__nonneg ... *)
    admit.
Admitted.


Module TupleTime.
    Definition HorribleDisaster: Type
     := Z * { po: Z | Zmod po 8 = 0 /\ 0 <= po }.

    Definition pointer_base (x: HorribleDisaster): Z := fst x.
    Definition pointer_offset (x: HorribleDisaster): Z := proj1_sig (snd x).

    Definition pointer_offset__align (x: HorribleDisaster):
        Zmod (pointer_offset x) 8 = 0
     := proj1 (proj2_sig (snd x)).

    Definition pointer_offset__nonneg (x: HorribleDisaster):
        0 <= pointer_offset x
     := proj2 (proj2_sig (snd x)).

    Definition build_HorribleDisaster (b o: Z)
        (Ho_align: Zmod o 8 = 0)
        (Ho_nonneg: 0 <= o):
        HorribleDisaster
     := (b, exist _ o (conj Ho_align Ho_nonneg)).

    Definition my_pointer: HorribleDisaster.
    apply (build_HorribleDisaster my_ptr_base my_ptr_offset).
    Proof.
        { (* Time to prove pointer_offset__align ... *) admit. }
        { (* Time to prove pointer_offset__nonneg ... *) admit. }
    Admitted.

    Program Definition my_other_pointer: HorribleDisaster
     := build_HorribleDisaster my_ptr_base my_ptr_offset _ _.
    Next Obligation.
        (* Time to prove pointer_offset__align ... *)
        admit.
    Admitted.
    Next Obligation.
        (* Time to prove pointer_offset__nonneg ... *)
        admit.
    Admitted.

    Lemma i_hate_destruct (x: HorribleDisaster):
        0 <= pointer_offset x.
    Proof.
        destruct x as [x_base [x_offset [Hx_offset__align Hx_offset__nonneg]]].
        exact Hx_offset__nonneg.
    Qed.
End TupleTime.