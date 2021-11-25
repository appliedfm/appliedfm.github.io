---
author: Tim Carstens
title:  "Working with records"
# date:   2021-11-21 22:00:00 -0800
categories: coq best-practices
---

Tips and tricks for using records in Coq.

# What's the difference between `Record` and `Structure`?

As far as Coq is concerned, [`Record` and `Structure` structure are synonyms](https://coq.inria.fr/refman/language/core/records.html#coq:cmd.Record). For Coq users this raises a question: which of these equivalent macros should I be using?

There is a strong argument that `Record` should be preferred:

* `Record` is shorter than `Structure`.
* The Coq documentation refers to records & structures alike as [_record types_](https://coq.inria.fr/refman/language/core/records.html).
* Many people use Coq to model the behavior of programming languages. Many of those languages have structured data (`struct` in C, `class` in Java, etc). With respect to nomenclature, it is often convenient to have different terminology when discussing types in Coq versus types in the languages we model in Coq, as in the following sentence: "The `timespec` structure from `time.h` is modeled by a record."
* In the author's experience, many syntax highlighting tools recognize `Record` but not `Structure`.



# Records as predicates

Records are a great way to bundle up a collection of predicates. To get the best results, though, it helps to know some tricks.

Consider the following example:

```coq
Record Foo: Type := {
    foo_x: nat;
    foo_y: nat;
}.

Record foo_valid (f: Foo): Prop := {
    foo_valid__y_nonzero: foo_y f <> 0;
}.
Arguments foo_valid__y_nonzero [_].


Definition inc_x (f: Foo): Foo := {|
    foo_x := 1 + foo_x f;
    foo_y := foo_y f;
|}.

Lemma inc_x__foo_valid (f: Foo)
    (Hf: foo_valid f):
    foo_valid (inc_x f).
Proof.
    (*
        This fails because `Hf` has type `foo_valid f`
        while the goal has type `foo_valid (inc_x f)`.
        
        This is annoying because `foo_valid` depends only
        on `foo_y`, which `inc_x` does not modify.
    *)
    Fail exact Hf.
    (*
        However, we can get past this problem by focusing
        directly on the projections.
        
        Note that the following tactic was written with
        maintenance in mind: if we later add a new
        projection to `foo_valid` that cannot be solved
        so easily, this tactic will leave those projections
        as unsolved goals rather than failing entirely.
    *)
    constructor ; try now destruct Hf.
Qed.
```
