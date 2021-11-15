---
# layout: post
title:  "Structures are better than tuples"
date:   2021-11-08 6:00:00 -0800
categories: coq best-practices
---

In our first post about Coq coding & proof style, we discuss the reasons to avoid excessive use of tuples.

For those following along, I'm using Coq 8.13.2 with the following imports:

```coq
Require Import Coq.ZArith.Zdiv.
Local Open Scope Z_scope.
```

# Tuples come in many bad forms

For various reasons, Coq has 3 tuple-like types:

* **Products**. This is what people usually mean when they say "tuple." They look simple but don't be fooled: they are actually very confusing. Quick, what does `snd (fst (1, 2, 4))` evaluate to? If you want to insert a new field between `2` and `4`, what changes would you need to make to this code?
* **Conjunction**. Sorry, but `P /\ Q` is just as bad as `P * Q` and `conj a b` is just as bad as `(a, b)`. Yes, I know the logic tactics know how to handle conjunction. No, I don't think that's a good enough reason to pay the tuple price.
* **Sigma**. It always looks so innocent in the beginning: `{ x: nat | x <> 0 }`. Then one day, someone needs to add an additional datum or condition. _No problem!_ they shout as they toss in a tuple up front and some `/\` in the back. Hope you like updating `match` and `destruct` patterns!

These types all suffer from the same maintenance problems:

1. They make the code less readable by filling it with generic names like `fst`, `snd`, `proj1`, `proj2`, `proj1_sig`, `proj2_sig`, `conj`, `exist`, etc. Excessive use of these functions makes it _very difficult_ to search/grep for call sites. They also inhibit readability by obscuring intent. They force engineers to remember which projections go with which types, which encourages proof engineers to write ad-hoc `destruct` patterns in their proofs, which further inhibits readability.
2. They make it difficult to amend or change definitions. This is especially bad for libraries: if you are a library maintainer and your public interfaces use tuples, you are basically _guaranteeing_ serious pain for your downstream users if you ever need to make changes.

In a collaborative engineering context it is imperative that we prioritize readability & maintainability. Excessive use of tuples works against this by making it harder for people to read, understand, maintain, and contribute to code.

Fortunately, tuples of all kinds can be replaced by `Structure`. Let's look at an example:

# Structures are great

```coq
Structure Pointer: Type := {
    pointer_base: Z;
    pointer_offset: Z;
    pointer_offset__align: Zmod pointer_offset 8 = 0;
    pointer_offset__nonneg: 0 <= pointer_offset;
}.
```

Now let me ask:

* Isn't that beautiful? Don't you just love how readable it is?
* Did you notice how _informative_ and _consistent_ the names are?
  * Did you notice the different conventions (`CamelCase` versus `snake_case`) for types and projections?
  * Can you guess the relationship between the name of the structure and the name of the projections?
  * Can you guess why `_` is used in some places and `__` in others?
  * When `__` is used, what do you notice about the stuff that comes before `__`? What about the stuff that comes after?
  * What does `` grep -n 'pointer_' `find ./ -name "*.v"` `` do?
  * What does `` grep -n 'pointer_offset__' `find ./ -name "*.v"` `` do?
* If you had to `destruct` one of these, what do you think the automatically generated names would be?
* If someone asked you to add or remove a field, do you think you'd know how to get started?

Anyway, let's try building one of these things.

As you can see, the special structure syntax (together with `refine` or `Program Definition`) yields code that is _extremely_ easy to maintain:

```coq
(* Using refine *)
Definition my_pointer: Pointer.
refine {|
    pointer_base := my_ptr_base;
    pointer_offset := my_ptr_offset;
    pointer_offset__align := _;
    pointer_offset__nonneg := _;
|}.
Proof.
  { (* Time to prove pointer_offset__align ... *) }
  { (* Time to prove pointer_offset__nonneg ... *) }
Qed.

(* Using Program Definition *)
Program Definition my_other_pointer: Pointer := {|
    pointer_base := my_other_ptr_base;
    pointer_offset := my_other_ptr_offset;
|}.
Next Obligation. (* Time to prove pointer_offset__align ... *) Qed.
Next Obligation. (* Time to prove pointer_offset__nonneg ... *) Qed.
```

So readable. So maintainable. You gotta love it.

# Just for comparison ...

Now let's build the same type using tuples and see how it compares.

First, note that we need to use a tuple, a conjunction, _and_ a sigma type to replicate `Pointer`:

```coq
Definition HorribleDisaster: Type
 := Z * { po: Z | Zmod po 8 = 0 /\ 0 <= po }.
```

I agree that this definition looks _cool_. However, every other definition around it looks _extremely uncool_. Let's start with the primitive projections:

```coq
Definition pointer_base (x: HorribleDisaster): Z := fst x.
Definition pointer_offset (x: HorribleDisaster): Z := proj1_sig (snd x).

Definition pointer_offset__align (x: HorribleDisaster):
    Zmod (pointer_offset x) 8 = 0
 := proj1 (proj2_sig (snd x)).

Definition pointer_offset__nonneg (x: HorribleDisaster):
    0 <= pointer_offset x
 := proj2 (proj2_sig (snd x)).
```

Oh my, looks like somebody had to figure out the right way to fit all those `fst`, `snd,` and `proj*_*` functions together. Glad I don't need to maintain _that_ code!

Now let's look at the constructor:

```coq
Definition Build_HorribleDisaster (b o: Z)
    (Ho_align: Zmod o 8 = 0)
    (Ho_nonneg: 0 <= o):
    HorribleDisaster
 := (b, exist _ o (conj Ho_align Ho_nonneg)).
```

This constructor can be used with `apply` and `Program Define`. However, since it does not have named fields, it is not as pleasant to use as the special structure syntax:
* The code is less intentional and therefore harder to casually read than its syntactic counterpart.
* It will be tedious to modify if we ever want to add another field to our type.
* Nothing about this code jumps out as "building a structure:" if you were scrolling by quickly, it'd look like any other function or lemma.

Take a look:

```coq
Definition my_pointer: HorribleDisaster.
apply (build_HorribleDisaster my_ptr_base my_ptr_offset).
Proof.
    { (* Time to prove pointer_offset__align ... *) }
    { (* Time to prove pointer_offset__nonneg ... *) }
Qed.

Program Definition my_other_pointer: HorribleDisaster
 := build_HorribleDisaster my_ptr_base my_ptr_offset _ _.
Next Obligation. (* Time to prove pointer_offset__align ... *) Qed.
Next Obligation. (* Time to prove pointer_offset__nonneg ... *) Qed.
```

Destruct patterns are probably the worst thing about tuples. Let's take a look at the destruct pattern for this type:

```coq
Lemma i_hate_destruct (x: HorribleDisaster):
    0 <= pointer_offset x.
Proof.
    destruct x as [x_base [x_offset [Hx_offset__align Hx_offset__nonneg]]].
    exact Hx_offset__nonneg.
Qed.
```

Now imagine having to update _that_ pattern in a bunch of random files. Hope you like figuring out where the new `[` and `]` need to go!

# But what about standard library functions?

The standard library provides several useful combinators for working with tuples. This is especially true of list combinators, such as [`combine`](https://coq.inria.fr/library/Coq.Lists.List.html#combine).

However, the benefit of reusing these combinators is outweighed by the cost of maintaining code that relies too heavily on tuples.

In my experience, you're going to need to define some helper lemmas _no matter which data structure you use_, so you might as well use a data structure that's easy to read & maintain. _Code reuse is good, but not if it obfuscates readability or intent._

# Conclusion

Structures are better than tuples.
