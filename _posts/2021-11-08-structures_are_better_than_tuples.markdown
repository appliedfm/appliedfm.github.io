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
* **Sigma**. It always looks so innocent in the beginning: `{ x: nat | x <> 0 }`. Then one day, someone needs to add an additional datum or condition. _No problem!_ they shout as they toss in a product up front and some `/\` in the back. Hope you like updating `match` and `destruct` patterns!

These types all suffer from the same maintenance problems:

1. They make the code less readable by filling it with generic names like `fst`, `snd`, `proj1`, `proj2`, `proj1_sig`, `proj2_sig`, `conj`, `exist`, (we will look at some examples in a bit). Excessive use of these functions makes it _very difficult_ to search/grep for call sites. They also inhibit readability by obscuring intent. They force engineers to remember which projections go with which types, which encourages proof engineers to write ad-hoc `destruct` patterns in their proofs, which further inhibits readability.
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

* Don't you love how readable it is?
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

The special structure syntax (together with either `refine` or `Program Definition`) yields code that is _extremely_ easy to maintain:

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
  { (* pointer_offset__align ... *) }
  { (* pointer_offset__nonneg ... *) }
Qed.

(* Alternative approach using Program Definition *)
Program Definition my_other_pointer: Pointer := {|
    pointer_base := my_other_ptr_base;
    pointer_offset := my_other_ptr_offset;
|}.
Next Obligation. (* pointer_offset__align ... *) Qed.
Next Obligation. (* pointer_offset__nonneg ... *) Qed.
```

So readable. So maintainable.

But that's not all! Structures also interact nicely with `match ... end`. In this next example we match on _some_ of the structure's fields:

```coq
Definition pointer_base_is_zero (x: Pointer):
    bool
 := match x with
    | {| pointer_base := 0 |} => true
    | _ => false
    end.
```

This was an easy function to write: I did not need to remind myself how to construct a `Pointer`; I just needed the name of the field I cared about.

# Tuples are not great

Now let's build the same type using tuples and see how it compares.

First, note that we need to use a product, a conjunction, _and_ a sigma type to replicate `Pointer`:

```coq
Definition HorribleDisaster: Type
 := Z * { po: Z | Zmod po 8 = 0 /\ 0 <= po }.
```

I agree that this definition looks _cool_. However, every other definition around it looks _extremely uncool_. Let's start with the primitive projections:

```coq
Definition pointer_base (x: HorribleDisaster): Z
 := fst x.
Definition pointer_offset (x: HorribleDisaster): Z
 := proj1_sig (snd x).

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
(* Using apply *)
Definition my_pointer: HorribleDisaster.
apply (build_HorribleDisaster my_ptr_base my_ptr_offset).
Proof.
    { (* pointer_offset__align ... *) }
    { (* pointer_offset__nonneg ... *) }
Qed.

(* Alternative approach using Program Definition *)
Program Definition my_other_pointer: HorribleDisaster
 := build_HorribleDisaster my_ptr_base my_ptr_offset _ _.
Next Obligation. (* pointer_offset__align ... *) Qed.
Next Obligation. (* pointer_offset__nonneg ... *) Qed.
```

Lastly, destruct patterns are probably the worst thing about tuples:

```coq
Lemma i_hate_destruct (x: HorribleDisaster):
    0 <= pointer_offset x.
Proof.
    destruct x as [
        x_base
        [
            x_offset
            [
                Hx_offset__align
                Hx_offset__nonneg
            ]
        ]
    ].
    exact Hx_offset__nonneg.
Qed.
```

This is bad:
* Even when it all fits on one line, there's no pretty way to format it. Tuples are all about _pairs_, and if you have more than 2 things you care about, you're going to have a problem making the `[` and `]` look nice.
* If we ever need to add a field to the `HorribleDisaster` type, this pattern would be obnoxious to edit.
* This pattern is 10 lines long (in contrast to the definition of the `Pointer` structure, which is only 6 lines long.)

Unfortunately, these challenges apply to `match ... end` patterns as well.

# What about standard library functions?

The standard library provides several useful combinators for working with tuples. This is especially true of list functions such as [`combine`](https://coq.inria.fr/library/Coq.Lists.List.html#combine).

However, the benefit of reusing these combinators is outweighed by the cost of maintaining code that relies too heavily on tuples.

In my experience, you're going to need to define some helper lemmas _no matter which data structure you use_, so you might as well use a data structure that's easy to read & maintain. _Code reuse is good, but not if it obfuscates readability or intent._

# Can I use tuples internally but expose a non-tuple interface publicly?

If you really want to, sure. There are several ways to hide tuples:

* Type classes
* Modules
* Opaque definitions

However, these approaches won't get you the benefits of structure syntax for construction and pattern matching. Keep this in mind as you design your public interface.

(If you've had success with this, please reach out!)

# Conclusion

* Communicating intent
    * Tuples obfuscate intent by filling code with generic projections & constructors (`fst`, `proj1`, `proj1_sig`, `conj`, `exist`, etc).
    * Structures communicate intent through named fields.
* Construction
    * Tuples are hard to construct because they're often the wrong "shape" for the data.
    * Structures are easy to construct because there's a special syntax for doing so.
* Projection
    * Tuples force you to write your own projections. This is tedious.
    * Structures provide projections automatically.
* Matching & destructing
    * Tuples are hard to match & destruct due to their shape.
    * Structures are easier to destruct and even easier to `match ... end`.

Structures are better than tuples.
