---
title     : "Denotational: Denotational semantics of untyped lambda calculus"
layout    : page
prev      : /BigStep/
permalink : /Denotational/
next      : /Compositional/
---

```
module plfa.part3.Denotational where
```

The lambda calculus is a language about _functions_, that is, mappings
from input to output. In computing we often think of such
mappings as being carried out by a sequence of
operations that transform an input into an output.  But
functions can also be represented as data. For example, one
can tabulate a function, that is, create a table where each row has
two entries, an input and the corresponding output for the function.
Function application is then the process of looking up the row for
a given input and reading off the output.

We shall create a semantics for the untyped lambda calculus based on
this idea of functions-as-tables. However, there are two difficulties
that arise. First, functions often have an infinite domain, so it
would seem that we would need infinitely long tables to represent
functions. Second, in the lambda calculus, functions can be applied to
functions. They can even be applied to themselves! So it would seem
that the tables would contain cycles. One might start to worry that
advanced techniques are necessary to address these issues, but
fortunately this is not the case!

The first problem, of functions with infinite domains, is solved by
observing that in the execution of a terminating program, each lambda
abstraction will only be applied to a finite number of distinct
arguments. (We come back later to discuss diverging programs.) This
observation is another way of looking at Dana Scott's insight that
only continuous functions are needed to model the lambda calculus.

The second problem, that of self-application, is solved by relaxing
the way in which we lookup an argument in a function's table.
Naively, one would look in the table for a row in which the input
entry exactly matches the argument. In the case of self-application,
this would require the table to contain a copy of itself. Impossible!
(At least, it is impossible if we want to build tables using inductive
data type definitions, which indeed we do.)  Instead it is sufficient
to find an input such that every row of the input appears as a row of
the argument (that is, the input is a subset of the argument).  In the
case of self-application, the table only needs to contain a smaller
copy of itself, which is fine.

With these two observations in hand, it is straightforward to write
down a denotational semantics of the lambda calculus.

## Imports

```
open import Agda.Primitive using (lzero; lsuc)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂; cong-app)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Function using (_∘_)
open import plfa.part2.Untyped
  using (Context; ★; _∋_; ∅; _,_; Z; S_; _⊢_; `_; _·_; ƛ_;
         #_; twoᶜ; plusᶜ; ext; rename; exts; subst; subst-zero; _[_])
open import plfa.part2.Substitution using (Rename; extensionality; rename-id)
```


## Values

The `Value` data type represents a finite portion of a function.  We
think of a value as a finite set of pairs that represent input-output
mappings. The `Value` data type represents the set as a binary tree
whose internal nodes are the union operator and whose leaves represent
either a single mapping or the empty set.

  * The ⊥ value provides no information about the computation.

  * A value of the form `v ↦ w` is a single input-output mapping, from
    input `v` to output `w`.

  * A value of the form `v ⊔ w` is a function that maps inputs to
    outputs according to both `v` and `w`.  Think of it as taking the
    union of the two sets.

```
infixr 7 _↦_
infixl 5 _⊔_

data Value : Set where
  ⊥ : Value
  _↦_ : Value → Value → Value
  _⊔_ : Value → Value → Value
```

The `⊑` relation adapts the familiar notion of subset to the Value data
type. This relation plays the key role in enabling self-application.
There are two rules that are specific to functions, `⊑-fun` and `⊑-dist`,
which we discuss below.

```
infix 4 _⊑_

data _⊑_ : Value → Value → Set where

  ⊑-bot : ∀ {v} → ⊥ ⊑ v

  ⊑-conj-L : ∀ {u v w}
    → v ⊑ u
    → w ⊑ u
      -----------
    → (v ⊔ w) ⊑ u

  ⊑-conj-R1 : ∀ {u v w}
    → u ⊑ v
      -----------
    → u ⊑ (v ⊔ w)

  ⊑-conj-R2 : ∀ {u v w}
    → u ⊑ w
      -----------
    → u ⊑ (v ⊔ w)

  ⊑-trans : ∀ {u v w}
    → u ⊑ v
    → v ⊑ w
      -----
    → u ⊑ w

  ⊑-fun : ∀ {v w v′ w′}
    → v′ ⊑ v
    → w ⊑ w′
      -------------------
    → (v ↦ w) ⊑ (v′ ↦ w′)

  ⊑-dist : ∀{v w w′}
      ---------------------------------
    → v ↦ (w ⊔ w′) ⊑ (v ↦ w) ⊔ (v ↦ w′)
```


The first five rules are straightforward.
The rule `⊑-fun` captures when it is OK to match a higher-order argument
`v′ ↦ w′` to a table entry whose input is `v ↦ w`.  Considering a
call to the higher-order argument. It is OK to pass a larger argument
than expected, so `v` can be larger than `v′`. Also, it is OK to
disregard some of the output, so `w` can be smaller than `w′`.
The rule `⊑-dist` says that if you have two entries for the same input,
then you can combine them into a single entry and joins the two
outputs.

The `⊑` relation is reflexive.

```
⊑-refl : ∀ {v} → v ⊑ v
⊑-refl {⊥} = ⊑-bot
⊑-refl {v ↦ v′} = ⊑-fun ⊑-refl ⊑-refl
⊑-refl {v₁ ⊔ v₂} = ⊑-conj-L (⊑-conj-R1 ⊑-refl) (⊑-conj-R2 ⊑-refl)
```

The `⊔` operation is monotonic with respect to `⊑`, that is, given two
larger values it produces a larger value.

```
⊔⊑⊔ : ∀ {v w v′ w′}
  → v ⊑ v′  →  w ⊑ w′
    -----------------------
  → (v ⊔ w) ⊑ (v′ ⊔ w′)
⊔⊑⊔ d₁ d₂ = ⊑-conj-L (⊑-conj-R1 d₁) (⊑-conj-R2 d₂)
```

The `⊑-dist` rule can be used to combine two entries even when the
input values are not identical. One can first combine the two inputs
using ⊔ and then apply the `⊑-dist` rule to obtain the following
property.

```
⊔↦⊔-dist : ∀{v v′ w w′ : Value}
  → (v ⊔ v′) ↦ (w ⊔ w′) ⊑ (v ↦ w) ⊔ (v′ ↦ w′)
⊔↦⊔-dist = ⊑-trans ⊑-dist (⊔⊑⊔ (⊑-fun (⊑-conj-R1 ⊑-refl) ⊑-refl)
                            (⊑-fun (⊑-conj-R2 ⊑-refl) ⊑-refl))
```

<!--
 [PLW: above might read more nicely if we introduce inequational reasoning.]
 -->

If the join `u ⊔ v` is less than another value `w`,
then both `u` and `v` are less than `w`.

```
⊔⊑-invL : ∀{u v w : Value}
  → u ⊔ v ⊑ w
    ---------
  → u ⊑ w
⊔⊑-invL (⊑-conj-L lt1 lt2) = lt1
⊔⊑-invL (⊑-conj-R1 lt) = ⊑-conj-R1 (⊔⊑-invL lt)
⊔⊑-invL (⊑-conj-R2 lt) = ⊑-conj-R2 (⊔⊑-invL lt)
⊔⊑-invL (⊑-trans lt1 lt2) = ⊑-trans (⊔⊑-invL lt1) lt2

⊔⊑-invR : ∀{u v w : Value}
  → u ⊔ v ⊑ w
    ---------
  → v ⊑ w
⊔⊑-invR (⊑-conj-L lt1 lt2) = lt2
⊔⊑-invR (⊑-conj-R1 lt) = ⊑-conj-R1 (⊔⊑-invR lt)
⊔⊑-invR (⊑-conj-R2 lt) = ⊑-conj-R2 (⊔⊑-invR lt)
⊔⊑-invR (⊑-trans lt1 lt2) = ⊑-trans (⊔⊑-invR lt1) lt2
```


## Environments

An environment gives meaning to the free variables in a term by
mapping variables to values.

```
Env : Context → Set
Env Γ = ∀ (x : Γ ∋ ★) → Value
```

We have the empty environment, and we can extend an environment.
```
`∅ : Env ∅
`∅ ()

infixl 5 _`,_

_`,_ : ∀ {Γ} → Env Γ → Value → Env (Γ , ★)
(γ `, v) Z = v
(γ `, v) (S x) = γ x
```

We can recover the previous environment from an extended environment,
and the last value. Putting them together again takes us back to where we started.
```
init : ∀ {Γ} → Env (Γ , ★) → Env Γ
init γ x = γ (S x)

last : ∀ {Γ} → Env (Γ , ★) → Value
last γ = γ Z

init-last : ∀ {Γ} → (γ : Env (Γ , ★)) → γ ≡ (init γ `, last γ)
init-last {Γ} γ = extensionality lemma
  where lemma : ∀ (x : Γ , ★ ∋ ★) → γ x ≡ (init γ `, last γ) x
        lemma Z      =  refl
        lemma (S x)  =  refl
```

We extend the `⊑` relation point-wise to environments with the
following definition.

```
_`⊑_ : ∀ {Γ} → Env Γ → Env Γ → Set
_`⊑_ {Γ} γ δ = ∀ (x : Γ ∋ ★) → γ x ⊑ δ x
```

We define a bottom environment and a join operator on environments,
which takes the point-wise join of their values.

```
`⊥ : ∀ {Γ} → Env Γ
`⊥ x = ⊥

_`⊔_ : ∀ {Γ} → Env Γ → Env Γ → Env Γ
(γ `⊔ δ) x = γ x ⊔ δ x
```

The `⊑-refl`, `⊑-conj-R1`, and `⊑-conj-R2` rules lift to environments.  So
the join of two environments `γ` and `δ` is greater than the first
environment `γ` or the second environment `δ`.

```
`⊑-refl : ∀ {Γ} {γ : Env Γ} → γ `⊑ γ
`⊑-refl {Γ} {γ} x = ⊑-refl {γ x}

⊑-env-conj-R1 : ∀ {Γ} → (γ : Env Γ) → (δ : Env Γ) → γ `⊑ (γ `⊔ δ)
⊑-env-conj-R1 γ δ x = ⊑-conj-R1 ⊑-refl

⊑-env-conj-R2 : ∀ {Γ} → (γ : Env Γ) → (δ : Env Γ) → δ `⊑ (γ `⊔ δ)
⊑-env-conj-R2 γ δ x = ⊑-conj-R2 ⊑-refl
```

## Denotational Semantics

We define the semantics with a judgment of the form `ρ ⊢ M ↓ v`,
where `ρ` is the environment, `M` the program, and `v` is a result value.
For readers familiar with big-step semantics, this notation will feel
quite natural, but don't let the similarity fool you.  There are
subtle but important differences! So here is the definition of the
semantics, which we discuss in detail in the following paragraphs.

```
infix 3 _⊢_↓_

data _⊢_↓_ : ∀{Γ} → Env Γ → (Γ ⊢ ★) → Value → Set where

  var : ∀ {Γ} {γ : Env Γ} {x}
      ---------------
    → γ ⊢ (` x) ↓ γ x

  ↦-elim : ∀ {Γ} {γ : Env Γ} {L M v w}
    → γ ⊢ L ↓ (v ↦ w)
    → γ ⊢ M ↓ v
      ---------------
    → γ ⊢ (L · M) ↓ w

  ↦-intro : ∀ {Γ} {γ : Env Γ} {N v w}
    → γ `, v ⊢ N ↓ w
      -------------------
    → γ ⊢ (ƛ N) ↓ (v ↦ w)

  ⊥-intro : ∀ {Γ} {γ : Env Γ} {M}
      ---------
    → γ ⊢ M ↓ ⊥

  ⊔-intro : ∀ {Γ} {γ : Env Γ} {M v w}
    → γ ⊢ M ↓ v
    → γ ⊢ M ↓ w
      ---------------
    → γ ⊢ M ↓ (v ⊔ w)

  sub : ∀ {Γ} {γ : Env Γ} {M v w}
    → γ ⊢ M ↓ v
    → w ⊑ v
      ---------
    → γ ⊢ M ↓ w
```

Consider the rule for lambda abstractions, `↦-intro`.  It says that a
lambda abstraction results in a single-entry table that maps the input
`v` to the output `w`, provided that evaluating the body in an
environment with `v` bound to its parameter produces the output `w`.
As a simple example of this rule, we can see that the identity function
maps `⊥` to `⊥` and also that it maps `⊥ ↦ ⊥` to `⊥ ↦ ⊥`.

```
id : ∅ ⊢ ★
id = ƛ # 0
```

```
denot-id1 : ∀ {γ} → γ ⊢ id ↓ ⊥ ↦ ⊥
denot-id1 = ↦-intro var

denot-id2 : ∀ {γ} → γ ⊢ id ↓ (⊥ ↦ ⊥) ↦ (⊥ ↦ ⊥)
denot-id2 = ↦-intro var
```

Of course, we will need tables with many rows to capture the meaning
of lambda abstractions. These can be constructed using the `⊔-intro`
rule.  If term M (typically a lambda abstraction) can produce both
tables `v` and `w`, then it produces the combined table `v ⊔ w`. One
can take an operational view of the rules `↦-intro` and `⊔-intro` by
imagining that when an interpreter first comes to a lambda
abstraction, it pre-evaluates the function on a bunch of randomly
chosen arguments, using many instances of the rule `↦-intro`, and then
joins them into a big table using many instances of the rule `⊔-intro`.
In the following we show that the identity function produces a table
containing both of the previous results, `⊥ ↦ ⊥` and
`(⊥ ↦ ⊥) ↦ (⊥ ↦ ⊥)`.

```
denot-id3 : `∅ ⊢ id ↓ (⊥ ↦ ⊥) ⊔ (⊥ ↦ ⊥) ↦ (⊥ ↦ ⊥)
denot-id3 = ⊔-intro denot-id1 denot-id2
```

We most often think of the judgment `γ ⊢ M ↓ v` as taking the
environment `γ` and term `M` as input, producing the result `v`.  However,
it is worth emphasizing that the semantics is a _relation_.  The above
results for the identity function show that the same environment and
term can be mapped to different results. However, the results for a
given `γ` and `M` are not _too_ different, they are all finite
approximations of the same function. Perhaps a better way of thinking
about the judgment `γ ⊢ M ↓ v` is that the `γ`, `M`, and `v` are all inputs
and the semantics either confirms or denies whether `v` is an accurate
partial description of the result of `M` in environment `γ`.

Next we consider the meaning of function application as given by the
`↦-elim` rule. In the premise of the rule we have that `L` maps `v` to
`w`. So if `M` produces `v`, then the application of `L` to `M`
produces `w`.

As an example of function application and the `↦-elim` rule, we apply
the identity function to itself.  Indeed, we have both that
`∅ ⊢ id ↓ (u ↦ u) ↦ (u ↦ u)` and also `∅ ⊢ id ↓ (u ↦ u)`, so we can
apply the rule `↦-elim`.

```
id-app-id : ∀ {u : Value} → `∅ ⊢ id · id ↓ (u ↦ u)
id-app-id {u} = ↦-elim (↦-intro var) (↦-intro var)
```

Next we revisit the Church numeral two: `λ f. λ u. (f (f u))`.
This function has two parameters: a function `f` and an arbitrary value
`u`, and it applies `f` twice. So `f` must map `u` to some value, which
we'll name `v`. Then for the second application,
`f` must map `v` to some value. Let's name it `w`. So the function's
table must include two entries, both `u ↦ v` and `v ↦ w`. For each
application of the table, we extract the appropriate entry from it
using the `sub` rule.  In particular, we use the ⊑-conj-R1 and
⊑-conj-R2 to select `u ↦ v` and `v ↦ w`, respectively, from the table
`u ↦ v ⊔ v ↦ w`. So the meaning of twoᶜ is that it takes this table
and parameter `u`, and it returns `w`.  Indeed we derive this as
follows.

```
denot-twoᶜ : ∀{u v w : Value} → `∅ ⊢ twoᶜ ↓ ((u ↦ v ⊔ v ↦ w) ↦ u ↦ w)
denot-twoᶜ {u}{v}{w} =
  ↦-intro (↦-intro (↦-elim (sub var lt1) (↦-elim (sub var lt2) var)))
  where lt1 : v ↦ w ⊑ u ↦ v ⊔ v ↦ w
        lt1 = ⊑-conj-R2 (⊑-fun ⊑-refl ⊑-refl)

        lt2 : u ↦ v ⊑ u ↦ v ⊔ v ↦ w
        lt2 = (⊑-conj-R1 (⊑-fun ⊑-refl ⊑-refl))
```


Next we have a classic example of self application: `Δ = λx. (x x)`.
The input value for `x` needs to be a table, and it needs to have an
entry that maps a smaller version of itself, call it `v`, to some value
`w`. So the input value looks like `v ↦ w ⊔ v`. Of course, then the
output of `Δ` is `w`. The derivation is given below.  The first occurrences
of `x` evaluates to `v ↦ w`, the second occurrence of `x` evaluates to `v`,
and then the result of the application is `w`.

```
Δ : ∅ ⊢ ★
Δ = (ƛ (# 0) · (# 0))

denot-Δ : ∀ {v w} → `∅ ⊢ Δ ↓ ((v ↦ w ⊔ v) ↦ w)
denot-Δ = ↦-intro (↦-elim (sub var (⊑-conj-R1 ⊑-refl))
                          (sub var (⊑-conj-R2 ⊑-refl)))
```

One might worry whether this semantics can deal with diverging
programs.  The `⊥` value and the `⊥-intro` rule provide a way to handle
them. (The `⊥-intro` rule is also what enables β reduction on
non-terminating arguments.)  The classic `Ω` program is a particularly
simple program that diverges. It applies `Δ` to itself. The semantics
assigns to `Ω` the meaning `⊥`. There are several ways to derive this, we
shall start with one that makes use of the `⊔-intro` rule.  First,
`denot-Δ` tells us that `Δ` evaluates to `((⊥ ↦ ⊥) ⊔ ⊥) ↦ ⊥`
(choose `v = w = ⊥`).  Next, `Δ` also evaluates to `⊥ ↦ ⊥` by use of
`↦-intro` and `⊥-intro` and to `⊥` by `⊥-intro`. As we saw previously,
whenever we can show that a program evaluates to two values, we can apply
`⊔-intro` to join them together, so `Δ` evaluates to `(⊥ ↦ ⊥) ⊔ ⊥`. This
matches the input of the first occurrence of `Δ`, so we can conclude that
the result of the application is `⊥`.

```
Ω : ∅ ⊢ ★
Ω = Δ · Δ

denot-Ω : `∅ ⊢ Ω ↓ ⊥
denot-Ω = ↦-elim denot-Δ (⊔-intro (↦-intro ⊥-intro) ⊥-intro)
```

A shorter derivation of the same result is by just one use of the
`⊥-intro` rule.

```
denot-Ω' : `∅ ⊢ Ω ↓ ⊥
denot-Ω' = ⊥-intro
```

Just because one can derive `∅ ⊢ M ↓ ⊥` for some closed term `M` doesn't mean
that `M` necessarily diverges. There may be other derivations that
conclude with `M` producing some more informative value.  However, if
the only thing that a term evaluates to is `⊥`, then it indeed diverges.

An attentive reader may have noticed a disconnect earlier in the way
we planned to solve the self-application problem and the actual
`↦-elim` rule for application. We said at the beginning that we would
relax the notion of table lookup, allowing an argument to match an
input entry if the argument is equal or greater than the input entry.
Instead, the `↦-elim` rule seems to require an exact match.  However,
because of the `sub` rule, application really does allow larger
arguments.

```
↦-elim2 : ∀ {Γ} {γ : Env Γ} {M₁ M₂ v₁ v₂ v₃}
  → γ ⊢ M₁ ↓ (v₁ ↦ v₃)
  → γ ⊢ M₂ ↓ v₂
  → v₁ ⊑ v₂
    ------------------
  → γ ⊢ (M₁ · M₂) ↓ v₃
↦-elim2 d₁ d₂ lt = ↦-elim d₁ (sub d₂ lt)
```

#### Exercise `denot-plusᶜ` (practice)

What is a denotation for `plusᶜ`? That is, find a value `v` (other than `⊥`)
such that `∅ ⊢ plusᶜ ↓ v`. Also, give the proof of `∅ ⊢ plusᶜ ↓ v`
for your choice of `v`.

```
-- Your code goes here
```


## Denotations and denotational equality

Next we define a notion of denotational equality based on the above
semantics. Its statement makes use of an if-and-only-if, which we
define as follows.

```
_iff_ : Set → Set → Set
P iff Q = (P → Q) × (Q → P)
```

Another way to view the denotational semantics is as a function that
maps a term to a relation from environments to values.  That is, the
_denotation_ of a term is a relation from environments to values.

```
Denotation : Context → Set₁
Denotation Γ = (Env Γ → Value → Set)
```

The following function ℰ gives this alternative view of the semantics,
which really just amounts to changing the order of the parameters.

```
ℰ : ∀{Γ} → (M : Γ ⊢ ★) → Denotation Γ
ℰ M = λ γ v → γ ⊢ M ↓ v
```

In general, two denotations are equal when they produce the same
values in the same environment.

```
infix 3 _≃_

_≃_ : ∀ {Γ} → (Denotation Γ) → (Denotation Γ) → Set
(_≃_ {Γ} D₁ D₂) = (γ : Env Γ) → (v : Value) → D₁ γ v iff D₂ γ v
```

Denotational equality is an equivalence relation.

```
≃-refl : ∀ {Γ : Context} → {M : Denotation Γ}
  → M ≃ M
≃-refl γ v = ⟨ (λ x → x) , (λ x → x) ⟩

≃-sym : ∀ {Γ : Context} → {M N : Denotation Γ}
  → M ≃ N
    -----
  → N ≃ M
≃-sym eq γ v = ⟨ (proj₂ (eq γ v)) , (proj₁ (eq γ v)) ⟩

≃-trans : ∀ {Γ : Context} → {M₁ M₂ M₃ : Denotation Γ}
  → M₁ ≃ M₂
  → M₂ ≃ M₃
    -------
  → M₁ ≃ M₃
≃-trans eq1 eq2 γ v = ⟨ (λ z → proj₁ (eq2 γ v) (proj₁ (eq1 γ v) z)) ,
                        (λ z → proj₂ (eq1 γ v) (proj₂ (eq2 γ v) z)) ⟩
```

Two terms `M` and `N` are denotational equal when their denotations are
equal, that is, `ℰ M ≃ ℰ N`.

The following submodule introduces equational reasoning for the `≃`
relation.

<!--

JGS: I couldn't get this to work. The definitions here were accepted
by Agda, but then the uses in the Compositional chapter got rejected.

denotation-setoid : Context → Setoid (lsuc lzero) lzero
denotation-setoid Γ = record
  { Carrier = Denotation Γ
  ; _≈_ = _≃_
  ; isEquivalence = record { refl = ≃-refl ; sym = ≃-sym ; trans = ≃-trans } }
-->
<!--
  The following went inside the module ≃-Reasoning:

  open import Relation.Binary.Reasoning.Setoid (denotation-setoid Γ)
    renaming (begin_ to start_; _≈⟨_⟩_ to _≃⟨_⟩_; _∎ to _☐) public
-->
```

module ≃-Reasoning {Γ : Context} where

  infix  1 start_
  infixr 2 _≃⟨⟩_ _≃⟨_⟩_
  infix  3 _☐

  start_ : ∀ {x y : Denotation Γ}
    → x ≃ y
      -----
    → x ≃ y
  start x≃y  =  x≃y

  _≃⟨_⟩_ : ∀ (x : Denotation Γ) {y z : Denotation Γ}
    → x ≃ y
    → y ≃ z
      -----
    → x ≃ z
  (x ≃⟨ x≃y ⟩ y≃z) =  ≃-trans x≃y y≃z

  _≃⟨⟩_ : ∀ (x : Denotation Γ) {y : Denotation Γ}
    → x ≃ y
      -----
    → x ≃ y
  x ≃⟨⟩ x≃y  =  x≃y

  _☐ : ∀ (x : Denotation Γ)
      -----
    → x ≃ x
  (x ☐)  =  ≃-refl
```

## Road map for the following chapters

The subsequent chapters prove that the denotational semantics has
several desirable properties. First, we prove that the semantics is
compositional, i.e., that the denotation of a term is a function of
the denotations of its subterms. To do this we shall prove equations
of the following shape.

    ℰ (` x) ≃ ...
    ℰ (ƛ M) ≃ ... ℰ M ...
    ℰ (M · N) ≃ ... ℰ M ... ℰ N ...

The compositionality property is not trivial because the semantics we
have defined includes three rules that are not syntax directed:
`⊥-intro`, `⊔-intro`, and `sub`. The above equations suggest that the
denotational semantics can be defined as a recursive function, and
indeed, we give such a definition and prove that it is equivalent to
ℰ.

Next we investigate whether the denotational semantics and the
reduction semantics are equivalent. Recall that the job of a language
semantics is to describe the observable behavior of a given program
`M`. For the lambda calculus there are several choices that one can
make, but they usually boil down to a single bit of information:

  * divergence: the program `M` executes forever.
  * termination: the program `M` halts.

We can characterize divergence and termination in terms of reduction.

  * divergence: `¬ (M —↠ ƛ N)` for any term `N`.
  * termination: `M —↠ ƛ N` for some term `N`.

We can also characterize divergence and termination using denotations.

  * divergence: `¬ (∅ ⊢ M ↓ v ↦ w)` for any `v` and `w`.
  * termination: `∅ ⊢ M ↓ v ↦ w` for some `v` and `w`.

Alternatively, we can use the denotation function `ℰ`.

  * divergence: `¬ (ℰ M ≃ ℰ (ƛ N))` for any term `N`.
  * termination: `ℰ M ≃ ℰ (ƛ N)` for some term `N`.

So the question is whether the reduction semantics and denotational
semantics are equivalent.

    (∃ N. M —↠ ƛ N)  iff  (∃ N. ℰ M ≃ ℰ (ƛ N))

We address each direction of the equivalence in the second and third
chapters. In the second chapter we prove that reduction to a lambda
abstraction implies denotational equality to a lambda
abstraction. This property is called the _soundness_ in the
literature.

    M —↠ ƛ N  implies  ℰ M ≃ ℰ (ƛ N)

In the third chapter we prove that denotational equality to a lambda
abstraction implies reduction to a lambda abstraction. This property
is called _adequacy_ in the literature.

    ℰ M ≃ ℰ (ƛ N)  implies M —↠ ƛ N′ for some N′

The fourth chapter applies the results of the three preceding
chapters (compositionality, soundness, and adequacy) to prove that
denotational equality implies a property called _contextual
equivalence_. This property is important because it justifies the use
of denotational equality in proving the correctness of program
transformations such as performance optimizations.

The proofs of all of these properties rely on some basic results about
the denotational semantics, which we establish in the rest of this
chapter.  We start with some lemmas about renaming, which are quite
similar to the renaming lemmas that we have seen in previous chapters.
We conclude with a proof of an important inversion lemma for the
less-than relation regarding function values.


## Renaming preserves denotations

We shall prove that renaming variables, and changing the environment
accordingly, preserves the meaning of a term. We generalize the
renaming lemma to allow the values in the new environment to be the
same or larger than the original values. This generalization is useful
in proving that reduction implies denotational equality.

As before, we need an extension lemma to handle the case where we
proceed underneath a lambda abstraction. Suppose that `ρ` is a
renaming that maps variables in `γ` into variables with equal or
larger values in `δ`. This lemma says that extending the renaming
produces a renaming `ext r` that maps `γ , v` to `δ , v`.

```
ext-⊑ : ∀ {Γ Δ v} {γ : Env Γ} {δ : Env Δ}
  → (ρ : Rename Γ Δ)
  → γ `⊑ (δ ∘ ρ)
    ------------------------------
  → (γ `, v) `⊑ ((δ `, v) ∘ ext ρ)
ext-⊑ ρ lt Z = ⊑-refl
ext-⊑ ρ lt (S n′) = lt n′
```

We proceed by cases on the de Bruijn index `n`.

* If it is `Z`, then we just need to show that `v ≡ v`, which we have by `refl`.

* If it is `S n′`, then the goal simplifies to `γ n′ ≡ δ (ρ n′)`,
  which is an instance of the premise.

Now for the renaming lemma. Suppose we have a renaming that maps
variables in `γ` into variables with the same values in `δ`.  If `M`
results in `v` when evaluated in environment `γ`, then applying the
renaming to `M` produces a program that results in the same value `v` when
evaluated in `δ`.

```
rename-pres : ∀ {Γ Δ v} {γ : Env Γ} {δ : Env Δ} {M : Γ ⊢ ★}
  → (ρ : Rename Γ Δ)
  → γ `⊑ (δ ∘ ρ)
  → γ ⊢ M ↓ v
    ---------------------
  → δ ⊢ (rename ρ M) ↓ v
rename-pres ρ lt (var {x = x}) = sub var (lt x)
rename-pres ρ lt (↦-elim d d₁) =
   ↦-elim (rename-pres ρ lt d) (rename-pres ρ lt d₁)
rename-pres ρ lt (↦-intro d) =
   ↦-intro (rename-pres (ext ρ) (ext-⊑ ρ lt) d)
rename-pres ρ lt ⊥-intro = ⊥-intro
rename-pres ρ lt (⊔-intro d d₁) =
   ⊔-intro (rename-pres ρ lt d) (rename-pres ρ lt d₁)
rename-pres ρ lt (sub d lt′) =
   sub (rename-pres ρ lt d) lt′
```

The proof is by induction on the semantics of `M`.  As you can see, all
of the cases are trivial except the cases for variables and lambda.

* For a variable `x`, we make use of the premise to show that
  `γ x ≡ δ (ρ x)`.

* For a lambda abstraction, the induction hypothesis requires us to
  extend the renaming. We do so, and use the `ext-⊑` lemma to show
  that the extended renaming maps variables to ones with equivalent
  values.


## Environment strengthening and identity renaming

We shall need a corollary of the renaming lemma that says that
replacing the environment with a larger one (a stronger one) does not
change whether a term `M` results in particular value `v`. In
particular, if `γ ⊢ M ↓ v` and `γ ⊑ δ`, then `δ ⊢ M ↓ v`.  What does
this have to do with renaming?  It's renaming with the identity
function.  We apply the renaming lemma with the identity renaming,
which gives us `δ ⊢ rename (λ {A} x → x) M ↓ v`, and then we apply the
`rename-id` lemma to obtain `δ ⊢ M ↓ v`.

```
⊑-env : ∀ {Γ} {γ : Env Γ} {δ : Env Γ} {M v}
  → γ ⊢ M ↓ v
  → γ `⊑ δ
    ----------
  → δ ⊢ M ↓ v
⊑-env{Γ}{γ}{δ}{M}{v} d lt
      with rename-pres{Γ}{Γ}{v}{γ}{δ}{M} (λ {A} x → x) lt d
... | δ⊢id[M]↓v rewrite rename-id {Γ}{★}{M} =
      δ⊢id[M]↓v
```

In the proof that substitution reflects denotations, in the case for
lambda abstraction, we use a minor variation of `⊑-env`, in which just
the last element of the environment gets larger.

```
up-env : ∀ {Γ} {γ : Env Γ} {M v u₁ u₂}
  → (γ `, u₁) ⊢ M ↓ v
  → u₁ ⊑ u₂
    -----------------
  → (γ `, u₂) ⊢ M ↓ v
up-env d lt = ⊑-env d (ext-le lt)
  where
  ext-le : ∀ {γ u₁ u₂} → u₁ ⊑ u₂ → (γ `, u₁) `⊑ (γ `, u₂)
  ext-le lt Z = lt
  ext-le lt (S n) = ⊑-refl
```

#### Exercise `denot-church` (recommended)

Church numerals are more general than natural numbers in that they
represent paths. A path consists of `n` edges and `n + 1` vertices.
We store the vertices in a vector of length `n + 1` in reverse
order. The edges in the path map the ith vertex to the `i + 1` vertex.
The following function `D^suc` (for denotation of successor) constructs
a table whose entries are all the edges in the path.

```
D^suc : (n : ℕ) → Vec Value (suc n) → Value
D^suc zero (a[0] ∷ []) = ⊥
D^suc (suc i) (a[i+1] ∷ a[i] ∷ ls) =  a[i] ↦ a[i+1]  ⊔  D^suc i (a[i] ∷ ls)
```

We use the following auxiliary function to obtain the last element of
a non-empty vector. (This formulation is more convenient for our
purposes than the one in the Agda standard library.)

```
vec-last : ∀{n : ℕ} → Vec Value (suc n) → Value
vec-last {0} (a ∷ []) = a
vec-last {suc n} (a ∷ b ∷ ls) = vec-last (b ∷ ls)
```

The function `Dᶜ` computes the denotation of the nth Church numeral
for a given path.

```
Dᶜ : (n : ℕ) → Vec Value (suc n) → Value
Dᶜ n (a[n] ∷ ls) = (D^suc n (a[n] ∷ ls)) ↦ (vec-last (a[n] ∷ ls)) ↦ a[n]
```

* The Church numeral for 0 ignores its first argument and returns
  its second argument, so for the singleton path consisting of
  just `a[0]`, its denotation is

        ⊥ ↦ a[0] ↦ a[0]

* The Church numeral for `suc n` takes two arguments:
  a successor function whose denotation is given by `D^suc`,
  and the start of the path (last of the vector).
  It returns the `n + 1` vertex in the path.

        (D^suc (suc n) (a[n+1] ∷ a[n] ∷ ls)) ↦ (vec-last (a[n] ∷ ls)) ↦ a[n+1]

The exercise is to prove that for any path `ls`, the meaning of the
Church numeral `n` is `Dᶜ n ls`.

To facilitate talking about arbitrary Church numerals, the following
`church` function builds the term for the nth Church numeral,
using the auxiliary function `apply-n`.

```
apply-n : (n : ℕ) → ∅ , ★ , ★ ⊢ ★
apply-n zero = # 0
apply-n (suc n) = # 1 · apply-n n

church : (n : ℕ) → ∅ ⊢ ★
church n = ƛ ƛ apply-n n
```

Prove the following theorem.

    denot-church : ∀{n : ℕ}{ls : Vec Value (suc n)}
       → `∅ ⊢ church n ↓ Dᶜ n ls

```
-- Your code goes here
```


## Inversion of the less-than relation for functions

What can we deduce from knowing that a function `v ↦ w` is less than
some value `u`?  What can we deduce about `u`? The answer to this
question is called the inversion property of less-than for functions.
This question is not easy to answer because of the `⊑-dist` rule, which
relates a function on the left to a pair of functions on the right.
So `u` may include several functions that, as a group, relate to
`v ↦ w`. Furthermore, because of the rules `⊑-conj-R1` and `⊑-conj-R2`,
there may be other values inside `u`, such as `⊥`, that have nothing
to do with `v ↦ w`. But in general, we can deduce that `u` includes
a collection of functions where the join of their domains is less
than `v` and the join of their codomains is greater than `w`.

To precisely state and prove this inversion property, we need to
define what it means for a value to _include_ a collection of values.
We also need to define how to compute the join of their domains and
codomains.


### Value membership and inclusion

Recall that we think of a value as a set of entries with the join
operator `v ⊔ w` acting like set union. The function value `v ↦ w` and
bottom value `⊥` constitute the two kinds of elements of the set.  (In
other contexts one can instead think of `⊥` as the empty set, but here
we must think of it as an element.)  We write `u ∈ v` to say that `u` is
an element of `v`, as defined below.

```
infix 5 _∈_

_∈_ : Value → Value → Set
u ∈ ⊥ = u ≡ ⊥
u ∈ v ↦ w = u ≡ v ↦ w
u ∈ (v ⊔ w) = u ∈ v ⊎ u ∈ w
```

So we can represent a collection of values simply as a value.  We
write `v ⊆ w` to say that all the elements of `v` are also in `w`.

```
infix 5 _⊆_

_⊆_ : Value → Value → Set
v ⊆ w = ∀{u} → u ∈ v → u ∈ w
```

The notions of membership and inclusion for values are closely related
to the less-than relation. They are narrower relations in that they
imply the less-than relation but not the other way around.

```
∈→⊑ : ∀{u v : Value}
    → u ∈ v
      -----
    → u ⊑ v
∈→⊑ {.⊥} {⊥} refl = ⊑-bot
∈→⊑ {v ↦ w} {v ↦ w} refl = ⊑-refl
∈→⊑ {u} {v ⊔ w} (inj₁ x) = ⊑-conj-R1 (∈→⊑ x)
∈→⊑ {u} {v ⊔ w} (inj₂ y) = ⊑-conj-R2 (∈→⊑ y)

⊆→⊑ : ∀{u v : Value}
    → u ⊆ v
      -----
    → u ⊑ v
⊆→⊑ {⊥} s with s {⊥} refl
... | x = ⊑-bot
⊆→⊑ {u ↦ u′} s with s {u ↦ u′} refl
... | x = ∈→⊑ x
⊆→⊑ {u ⊔ u′} s = ⊑-conj-L (⊆→⊑ (λ z → s (inj₁ z))) (⊆→⊑ (λ z → s (inj₂ z)))
```

We shall also need some inversion principles for value inclusion.  If
the union of `u` and `v` is included in `w`, then of course both `u` and
`v` are each included in `w`.

```
⊔⊆-inv : ∀{u v w : Value}
       → (u ⊔ v) ⊆ w
         ---------------
       → u ⊆ w  ×  v ⊆ w
⊔⊆-inv uvw = ⟨ (λ x → uvw (inj₁ x)) , (λ x → uvw (inj₂ x)) ⟩
```

In our value representation, the function value `v ↦ w` is both an
element and also a singleton set. So if `v ↦ w` is a subset of `u`,
then `v ↦ w` must be a member of `u`.

```
↦⊆→∈ : ∀{v w u : Value}
     → v ↦ w ⊆ u
       ---------
     → v ↦ w ∈ u
↦⊆→∈ incl = incl refl
```


### Function values

To identify collections of functions, we define the following two
predicates. We write `Fun u` if `u` is a function value, that is, if
`u ≡ v ↦ w` for some values `v` and `w`. We write `all-funs v` if all the elements
of `v` are functions.

```
data Fun : Value → Set where
  fun : ∀{u v w} → u ≡ (v ↦ w) → Fun u

all-funs : Value → Set
all-funs v = ∀{u} → u ∈ v → Fun u
```

The value `⊥` is not a function.

```
¬Fun⊥ : ¬ (Fun ⊥)
¬Fun⊥ (fun ())
```

In our values-as-sets representation, our sets always include at least
one element. Thus, if all the elements are functions, there is at
least one that is a function.

```
all-funs∈ : ∀{u}
      → all-funs u
      → Σ[ v ∈ Value ] Σ[ w ∈ Value ] v ↦ w ∈ u
all-funs∈ {⊥} f with f {⊥} refl
... | fun ()
all-funs∈ {v ↦ w} f = ⟨ v , ⟨ w , refl ⟩ ⟩
all-funs∈ {u ⊔ u′} f
    with all-funs∈ λ z → f (inj₁ z)
... | ⟨ v , ⟨ w , m ⟩ ⟩ = ⟨ v , ⟨ w , (inj₁ m) ⟩ ⟩
```


### Domains and codomains

Returning to our goal, the inversion principle for less-than a
function, we want to show that `v ↦ w ⊑ u` implies that `u` includes
a set of function values such that the join of their domains is less
than `v` and the join of their codomains is greater than `w`.

To this end we define the following `⨆dom` and `⨆cod` functions.  Given some
value `u` (that represents a set of entries), `⨆dom u` returns the join of
their domains and `⨆cod u` returns the join of their codomains.

```
⨆dom : (u : Value) → Value
⨆dom ⊥  = ⊥
⨆dom (v ↦ w) = v
⨆dom (u ⊔ u′) = ⨆dom u ⊔ ⨆dom u′

⨆cod : (u : Value) → Value
⨆cod ⊥  = ⊥
⨆cod (v ↦ w) = w
⨆cod (u ⊔ u′) = ⨆cod u ⊔ ⨆cod u′
```

We need just one property each for `⨆dom` and `⨆cod`.  Given a collection of
functions represented by value `u`, and an entry `v ↦ w ∈ u`, we know
that `v` is included in the domain of `u`.

```
↦∈→⊆⨆dom : ∀{u v w : Value}
          → all-funs u  →  (v ↦ w) ∈ u
            ----------------------
          → v ⊆ ⨆dom u
↦∈→⊆⨆dom {⊥} fg () u∈v
↦∈→⊆⨆dom {v ↦ w} fg refl u∈v = u∈v
↦∈→⊆⨆dom {u ⊔ u′} fg (inj₁ v↦w∈u) u∈v =
   let ih = ↦∈→⊆⨆dom (λ z → fg (inj₁ z)) v↦w∈u in
   inj₁ (ih u∈v)
↦∈→⊆⨆dom {u ⊔ u′} fg (inj₂ v↦w∈u′) u∈v =
   let ih = ↦∈→⊆⨆dom (λ z → fg (inj₂ z)) v↦w∈u′ in
   inj₂ (ih u∈v)
```

Regarding `⨆cod`, suppose we have a collection of functions represented
by `u`, but all of them are just copies of `v ↦ w`.  Then the `⨆cod u` is
included in `w`.

```
⊆↦→⨆cod⊆ : ∀{u v w : Value}
        → u ⊆ v ↦ w
          ---------
        → ⨆cod u ⊆ w
⊆↦→⨆cod⊆ {⊥} s refl with s {⊥} refl
... | ()
⊆↦→⨆cod⊆ {C ↦ C′} s m with s {C ↦ C′} refl
... | refl = m
⊆↦→⨆cod⊆ {u ⊔ u′} s (inj₁ x) = ⊆↦→⨆cod⊆ (λ {C} z → s (inj₁ z)) x
⊆↦→⨆cod⊆ {u ⊔ u′} s (inj₂ y) = ⊆↦→⨆cod⊆ (λ {C} z → s (inj₂ z)) y
```

With the `⨆dom` and `⨆cod` functions in hand, we can make precise the
conclusion of the inversion principle for functions, which we package
into the following predicate named `factor`. We say that `v ↦ w`
_factors_ `u` into `u′` if `u′` is included in `u`, if `u′` contains only
functions, its domain is less than `v`, and its codomain is greater
than `w`.

```
factor : (u : Value) → (u′ : Value) → (v : Value) → (w : Value) → Set
factor u u′ v w = all-funs u′  ×  u′ ⊆ u  ×  ⨆dom u′ ⊑ v  ×  w ⊑ ⨆cod u′
```

So the inversion principle for functions can be stated as

      v ↦ w ⊑ u
      ---------------
    → factor u u′ v w

We prove the inversion principle for functions by induction on the
derivation of the less-than relation. To make the induction hypothesis
stronger, we broaden the premise `v ↦ w ⊑ u` to `u₁ ⊑ u₂`, and
strengthen the conclusion to say that for _every_ function value
`v ↦ w ∈ u₁`, we have that `v ↦ w` factors `u₂` into some value `u₃`.

    → u₁ ⊑ u₂
      ------------------------------------------------------
    → ∀{v w} → v ↦ w ∈ u₁ → Σ[ u₃ ∈ Value ] factor u₂ u₃ v w


### Inversion of less-than for functions, the case for ⊑-trans

The crux of the proof is the case for `⊑-trans`.

    u₁ ⊑ u   u ⊑ u₂
    --------------- (⊑-trans)
        u₁ ⊑ u₂

By the induction hypothesis for `u₁ ⊑ u`, we know
that `v ↦ w factors u into u′`, for some value `u′`,
so we have `all-funs u′` and `u′ ⊆ u`.
By the induction hypothesis for `u ⊑ u₂`, we know
that for any `v′ ↦ w′ ∈ u`, `v′ ↦ w′` factors `u₂` into `u₃`.
With these facts in hand, we proceed by induction on `u′`
to prove that `(⨆dom u′) ↦ (⨆cod u′)` factors `u₂` into `u₃`.
We discuss each case of the proof in the text below.

```
sub-inv-trans : ∀{u′ u₂ u : Value}
    → all-funs u′  →  u′ ⊆ u
    → (∀{v′ w′} → v′ ↦ w′ ∈ u → Σ[ u₃ ∈ Value ] factor u₂ u₃ v′ w′)
      ---------------------------------------------------------------
    → Σ[ u₃ ∈ Value ] factor u₂ u₃ (⨆dom u′) (⨆cod u′)
sub-inv-trans {⊥} {u₂} {u} fu′ u′⊆u IH =
   ⊥-elim (contradiction (fu′ refl) ¬Fun⊥)
sub-inv-trans {u₁′ ↦ u₂′} {u₂} {u} fg u′⊆u IH = IH (↦⊆→∈ u′⊆u)
sub-inv-trans {u₁′ ⊔ u₂′} {u₂} {u} fg u′⊆u IH
    with ⊔⊆-inv u′⊆u
... | ⟨ u₁′⊆u , u₂′⊆u ⟩
    with sub-inv-trans {u₁′} {u₂} {u} (λ {v′} z → fg (inj₁ z)) u₁′⊆u IH
       | sub-inv-trans {u₂′} {u₂} {u} (λ {v′} z → fg (inj₂ z)) u₂′⊆u IH
... | ⟨ u₃₁ , ⟨ fu21' , ⟨ u₃₁⊆u₂ , ⟨ du₃₁⊑du₁′ , cu₁′⊑cu₃₁ ⟩ ⟩ ⟩ ⟩
    | ⟨ u₃₂ , ⟨ fu22' , ⟨ u₃₂⊆u₂ , ⟨ du₃₂⊑du₂′ , cu₁′⊑cu₃₂ ⟩ ⟩ ⟩ ⟩ =
      ⟨ (u₃₁ ⊔ u₃₂) , ⟨ fu₂′ , ⟨ u₂′⊆u₂ ,
      ⟨ ⊔⊑⊔ du₃₁⊑du₁′ du₃₂⊑du₂′ ,
        ⊔⊑⊔ cu₁′⊑cu₃₁ cu₁′⊑cu₃₂ ⟩ ⟩ ⟩ ⟩
    where fu₂′ : {v′ : Value} → v′ ∈ u₃₁ ⊎ v′ ∈ u₃₂ → Fun v′
          fu₂′ {v′} (inj₁ x) = fu21' x
          fu₂′ {v′} (inj₂ y) = fu22' y
          u₂′⊆u₂ : {C : Value} → C ∈ u₃₁ ⊎ C ∈ u₃₂ → C ∈ u₂
          u₂′⊆u₂ {C} (inj₁ x) = u₃₁⊆u₂ x
          u₂′⊆u₂ {C} (inj₂ y) = u₃₂⊆u₂ y
```

* Suppose `u′ ≡ ⊥`. Then we have a contradiction because
  it is not the case that `Fun ⊥`.

* Suppose `u′ ≡ u₁′ ↦ u₂′`. Then `u₁′ ↦ u₂′ ∈ u` and we can apply the
  premise (the induction hypothesis from `u ⊑ u₂`) to obtain that
  `u₁′ ↦ u₂′` factors of `u₂ into u₂′`. This case is complete because
  `⨆dom u′ ≡ u₁′` and `⨆cod u′ ≡ u₂′`.

* Suppose `u′ ≡ u₁′ ⊔ u₂′`. Then we have `u₁′ ⊆ u` and `u₂′ ⊆ u`. We also
  have `all-funs u₁′` and `all-funs u₂′`, so we can apply the induction hypothesis
  for both `u₁′` and `u₂′`. So there exists values `u₃₁` and `u₃₂` such that
  `(⨆dom u₁′) ↦ (⨆cod u₁′)` factors `u` into `u₃₁` and
  `(⨆dom u₂′) ↦ (⨆cod u₂′)` factors `u` into `u₃₂`.
  We will show that `(⨆dom u) ↦ (⨆cod u)` factors `u` into `u₃₁ ⊔ u₃₂`.
  So we need to show that

        ⨆dom (u₃₁ ⊔ u₃₂) ⊑ ⨆dom (u₁′ ⊔ u₂′)
        ⨆cod (u₁′ ⊔ u₂′) ⊑ ⨆cod (u₃₁ ⊔ u₃₂)

  But those both follow directly from the factoring of
  `u` into `u₃₁` and `u₃₂`, using the monotonicity of `⊔` with respect to `⊑`.


### Inversion of less-than for functions

We come to the proof of the main lemma concerning the inversion of
less-than for functions. We show that if `u₁ ⊑ u₂`, then for any
`v ↦ w ∈ u₁`, we can factor `u₂` into `u₃` according to `v ↦ w`. We proceed
by induction on the derivation of `u₁ ⊑ u₂`, and describe each case in
the text after the Agda proof.

```
sub-inv : ∀{u₁ u₂ : Value}
        → u₁ ⊑ u₂
        → ∀{v w} → v ↦ w ∈ u₁
          -------------------------------------
        → Σ[ u₃ ∈ Value ] factor u₂ u₃ v w
sub-inv {⊥} {u₂} ⊑-bot {v} {w} ()
sub-inv {u₁₁ ⊔ u₁₂} {u₂} (⊑-conj-L lt1 lt2) {v} {w} (inj₁ x) = sub-inv lt1 x
sub-inv {u₁₁ ⊔ u₁₂} {u₂} (⊑-conj-L lt1 lt2) {v} {w} (inj₂ y) = sub-inv lt2 y
sub-inv {u₁} {u₂₁ ⊔ u₂₂} (⊑-conj-R1 lt) {v} {w} m
    with sub-inv lt m
... | ⟨ u₃₁ , ⟨ fu₃₁ , ⟨ u₃₁⊆u₂₁ , ⟨ domu₃₁⊑v , w⊑codu₃₁ ⟩ ⟩ ⟩ ⟩ =
      ⟨ u₃₁ , ⟨ fu₃₁ , ⟨ (λ {w} z → inj₁ (u₃₁⊆u₂₁ z)) ,
                                   ⟨ domu₃₁⊑v , w⊑codu₃₁ ⟩ ⟩ ⟩ ⟩
sub-inv {u₁} {u₂₁ ⊔ u₂₂} (⊑-conj-R2 lt) {v} {w} m
    with sub-inv lt m
... | ⟨ u₃₂ , ⟨ fu₃₂ , ⟨ u₃₂⊆u₂₂ , ⟨ domu₃₂⊑v , w⊑codu₃₂ ⟩ ⟩ ⟩ ⟩ =
      ⟨ u₃₂ , ⟨ fu₃₂ , ⟨ (λ {C} z → inj₂ (u₃₂⊆u₂₂ z)) ,
                                   ⟨ domu₃₂⊑v , w⊑codu₃₂ ⟩ ⟩ ⟩ ⟩
sub-inv {u₁} {u₂} (⊑-trans{v = u} u₁⊑u u⊑u₂) {v} {w} v↦w∈u₁
    with sub-inv u₁⊑u v↦w∈u₁
... | ⟨ u′ , ⟨ fu′ , ⟨ u′⊆u , ⟨ domu′⊑v , w⊑codu′ ⟩ ⟩ ⟩ ⟩
    with sub-inv-trans {u′} fu′ u′⊆u (sub-inv u⊑u₂)
... | ⟨ u₃ , ⟨ fu₃ , ⟨ u₃⊆u₂ , ⟨ domu₃⊑domu′ , codu′⊑codu₃ ⟩ ⟩ ⟩ ⟩ =
      ⟨ u₃ , ⟨ fu₃ , ⟨ u₃⊆u₂ , ⟨ ⊑-trans domu₃⊑domu′ domu′⊑v ,
                                    ⊑-trans w⊑codu′ codu′⊑codu₃ ⟩ ⟩ ⟩ ⟩
sub-inv {u₁₁ ↦ u₁₂} {u₂₁ ↦ u₂₂} (⊑-fun lt1 lt2) refl =
    ⟨ u₂₁ ↦ u₂₂ , ⟨ (λ {w} → fun) , ⟨ (λ {C} z → z) , ⟨ lt1 , lt2 ⟩ ⟩ ⟩ ⟩
sub-inv {u₂₁ ↦ (u₂₂ ⊔ u₂₃)} {u₂₁ ↦ u₂₂ ⊔ u₂₁ ↦ u₂₃} ⊑-dist
    {.u₂₁} {.(u₂₂ ⊔ u₂₃)} refl =
    ⟨ u₂₁ ↦ u₂₂ ⊔ u₂₁ ↦ u₂₃ , ⟨ f , ⟨ g , ⟨ ⊑-conj-L ⊑-refl ⊑-refl , ⊑-refl ⟩ ⟩ ⟩ ⟩
  where f : all-funs (u₂₁ ↦ u₂₂ ⊔ u₂₁ ↦ u₂₃)
        f (inj₁ x) = fun x
        f (inj₂ y) = fun y
        g : (u₂₁ ↦ u₂₂ ⊔ u₂₁ ↦ u₂₃) ⊆ (u₂₁ ↦ u₂₂ ⊔ u₂₁ ↦ u₂₃)
        g (inj₁ x) = inj₁ x
        g (inj₂ y) = inj₂ y
```

Let `v` and `w` be arbitrary values.

* Case `⊑-bot`. So `u₁ ≡ ⊥`. We have `v ↦ w ∈ ⊥`, but that is impossible.

* Case `⊑-conj-L`.

        u₁₁ ⊑ u₂   u₁₂ ⊑ u₂
        -------------------
        u₁₁ ⊔ u₁₂ ⊑ u₂

  Given that `v ↦ w ∈ u₁₁ ⊔ u₁₂`, there are two subcases to consider.

  * Subcase `v ↦ w ∈ u₁₁`. We conclude by the induction
    hypothesis for `u₁₁ ⊑ u₂`.

  * Subcase `v ↦ w ∈ u₁₂`. We conclude by the induction hypothesis
    for `u₁₂ ⊑ u₂`.

* Case `⊑-conj-R1`.

        u₁ ⊑ u₂₁
        --------------
        u₁ ⊑ u₂₁ ⊔ u₂₂

  Given that `v ↦ w ∈ u₁`, the induction hypothesis for `u₁ ⊑ u₂₁`
  gives us that `v ↦ w` factors `u₂₁` into `u₃₁` for some `u₃₁`.
  To show that `v ↦ w` also factors `u₂₁ ⊔ u₂₂` into `u₃₁`,
  we just need to show that `u₃₁ ⊆ u₂₁ ⊔ u₂₂`, but that follows
  directly from `u₃₁ ⊆ u₂₁`.

* Case `⊑-conj-R2`. This case follows by reasoning similar to
  the case for `⊑-conj-R1`.

* Case `⊑-trans`.

        u₁ ⊑ u   u ⊑ u₂
        ---------------
            u₁ ⊑ u₂

  By the induction hypothesis for `u₁ ⊑ u`, we know
  that `v ↦ w` factors `u` into `u′`, for some value `u′`,
  so we have `all-funs u′` and `u′ ⊆ u`.
  By the induction hypothesis for `u ⊑ u₂`, we know
  that for any `v′ ↦ w′ ∈ u`, `v′ ↦ w′` factors `u₂`.
  Now we apply the lemma sub-inv-trans, which gives us
  some `u₃` such that `(⨆dom u′) ↦ (⨆cod u′)` factors `u₂` into `u₃`.
  We show that `v ↦ w` also factors `u₂` into `u₃`.
  From `⨆dom u₃ ⊑ ⨆dom u′` and `⨆dom u′ ⊑ v`, we have `⨆dom u₃ ⊑ v`.
  From `w ⊑ ⨆cod u′` and `⨆cod u′ ⊑ ⨆cod u₃`, we have `w ⊑ ⨆cod u₃`,
  and this case is complete.

* Case `⊑-fun`.

        u₂₁ ⊑ u₁₁  u₁₂ ⊑ u₂₂
        ---------------------
        u₁₁ ↦ u₁₂ ⊑ u₂₁ ↦ u₂₂

  Given that `v ↦ w ∈ u₁₁ ↦ u₁₂`, we have `v ≡ u₁₁` and `w ≡ u₁₂`.
  We show that `u₁₁ ↦ u₁₂` factors `u₂₁ ↦ u₂₂` into itself.
  We need to show that `⨆dom (u₂₁ ↦ u₂₂) ⊑ u₁₁` and `u₁₂ ⊑ ⨆cod (u₂₁ ↦ u₂₂)`,
  but that is equivalent to our premises `u₂₁ ⊑ u₁₁` and `u₁₂ ⊑ u₂₂`.

* Case `⊑-dist`.

        ---------------------------------------------
        u₂₁ ↦ (u₂₂ ⊔ u₂₃) ⊑ (u₂₁ ↦ u₂₂) ⊔ (u₂₁ ↦ u₂₃)

  Given that `v ↦ w ∈ u₂₁ ↦ (u₂₂ ⊔ u₂₃)`, we have `v ≡ u₂₁`
  and `w ≡ u₂₂ ⊔ u₂₃`.
  We show that `u₂₁ ↦ (u₂₂ ⊔ u₂₃)` factors `(u₂₁ ↦ u₂₂) ⊔ (u₂₁ ↦ u₂₃)`
  into itself. We have `u₂₁ ⊔ u₂₁ ⊑ u₂₁`, and also
  `u₂₂ ⊔ u₂₃ ⊑ u₂₂ ⊔ u₂₃`, so the proof is complete.


We conclude this section with two corollaries of the sub-inv lemma.
First, we have the following property that is convenient to use in
later proofs. We specialize the premise to just `v ↦ w ⊑ u₁`
and we modify the conclusion to say that for every
`v′ ↦ w′ ∈ u₂`, we have `v′ ⊑ v`.

```
sub-inv-fun : ∀{v w u₁ : Value}
    → (v ↦ w) ⊑ u₁
      -----------------------------------------------------
    → Σ[ u₂ ∈ Value ] all-funs u₂ × u₂ ⊆ u₁
        × (∀{v′ w′} → (v′ ↦ w′) ∈ u₂ → v′ ⊑ v) × w ⊑ ⨆cod u₂
sub-inv-fun{v}{w}{u₁} abc
    with sub-inv abc {v}{w} refl
... | ⟨ u₂ , ⟨ f , ⟨ u₂⊆u₁ , ⟨ db , cc ⟩ ⟩ ⟩ ⟩ =
      ⟨ u₂ , ⟨ f , ⟨ u₂⊆u₁ , ⟨ G , cc ⟩ ⟩ ⟩ ⟩
   where G : ∀{D E} → (D ↦ E) ∈ u₂ → D ⊑ v
         G{D}{E} m = ⊑-trans (⊆→⊑ (↦∈→⊆⨆dom f m)) db
```

The second corollary is the inversion rule that one would expect for
less-than with functions on the left and right-hand sides.

```
↦⊑↦-inv : ∀{v w v′ w′}
        → v ↦ w ⊑ v′ ↦ w′
          -----------------
        → v′ ⊑ v × w ⊑ w′
↦⊑↦-inv{v}{w}{v′}{w′} lt
    with sub-inv-fun lt
... | ⟨ Γ , ⟨ f , ⟨ Γ⊆v34 , ⟨ lt1 , lt2 ⟩ ⟩ ⟩ ⟩
    with all-funs∈ f
... | ⟨ u , ⟨ u′ , u↦u′∈Γ ⟩ ⟩
    with Γ⊆v34 u↦u′∈Γ
... | refl =
  let ⨆codΓ⊆w′ = ⊆↦→⨆cod⊆ Γ⊆v34 in
  ⟨ lt1 u↦u′∈Γ , ⊑-trans lt2 (⊆→⊑ ⨆codΓ⊆w′) ⟩
```


## Notes

The denotational semantics presented in this chapter is an example of
a _filter model_ (Barendregt, Coppo, Dezani-Ciancaglini, 1983). Filter
models use type systems with intersection types to precisely
characterize runtime behavior (Coppo, Dezani-Ciancaglini, and Salle,
1979). The notation that we use in this chapter is not that of type
systems and intersection types, but the `Value` data type is isomorphic
to types (`↦` is `→`, `⊔` is `∧`, `⊥` is `⊤`), the `⊑` relation is the
inverse of subtyping `<:`, and the evaluation relation `ρ ⊢ M ↓ v` is
isomorphic to a type system. Write `Γ` instead of `ρ`, `A` instead of `v`, and
replace `↓` with `:` and one has a typing judgement `Γ ⊢ M : A`.
By varying the definition of subtyping and using different choices of
type atoms, intersection type systems provide semantics for many different
untyped λ calculi, from full beta to the lazy and call-by-value calculi
(Alessi, Barbanera, and Dezani-Ciancaglini, 2006) (Rocca and Paolini, 2004).
The denotational semantics in this chapter corresponds to the BCD
system (Barendregt, Coppo, Dezani-Ciancaglini, 1983).  Part 3 of the
book _Lambda Calculus with Types_ describes a framework for
intersection type systems that enables results similar to the ones in
this chapter, but for the entire family of intersection type systems
(Barendregt, Dekkers, and Statman, 2013).

The two ideas of using finite tables to represent functions and of
relaxing table lookup to enable self application first appeared in a
technical report by Gordon Plotkin (1972) and are later described in
an article in Theoretical Computer Science (Plotkin 1993).  In that
work, the inductive definition of `Value` is a bit different than the
one we use:

    Value = C + ℘f(Value) × ℘f(Value)

where `C` is a set of constants and `℘f` means finite powerset.  The
pairs in `℘f(Value) × ℘f(Value)` represent input-output mappings, just
as in this chapter. The finite powersets are used to enable a function
table to appear in the input and in the output. These differences
amount to changing where the recursion appears in the definition of
`Value`.  Plotkin's model is an example of a _graph model_ of the
untyped lambda calculus (Barendregt, 1984). In a graph model, the
semantics is presented as a function from programs and environments to
(possibly infinite) sets of values. The semantics in this chapter is
instead defined as a relation, but set-valued functions are isomorphic
to relations. Indeed, we present the semantics as a function in the
next chapter and prove that it is equivalent to the relational
version.

Dana Scott's ℘(ω) (1976) and Engeler's B(A) (1981) are two more
examples of graph models. Both use the following inductive definition
of `Value`.

    Value = C + ℘f(Value) × Value

The use of `Value` instead of `℘f(Value)` in the output does not restrict
expressiveness compared to Plotkin's model because the semantics use
sets of values and a pair of sets `(V, V′)` can be represented as a set
of pairs `{ (V, v′) | v′ ∈ V′ }`.  In Scott's ℘(ω), the above values are
mapped to and from the natural numbers using a kind of Godel encoding.


## References

* Intersection Types and Lambda Models.  Fabio Alessi, Franco
  Barbanera, and Mariangiola Dezani-Ciancaglini, Theoretical
  Compututer Science, vol. 355, pages 108-126, 2006.

* The Lambda Calculus. H.P. Barendregt, 1984.

* A filter lambda model and the completeness of type assignment.  Henk
  Barendregt, Mario Coppo, and Mariangiola Dezani-Ciancaglini, Journal
  of Symbolic Logic, vol. 48, pages 931-940, 1983.

* Lambda Calculus with Types. Henk Barendregt, Wil Dekkers, and
  Richard Statman, Cambridge University Press, Perspectives in Logic,
  2013.

* Functional characterization of some semantic equalities inside
  λ-calculus. Mario Coppo, Mariangiola Dezani-Ciancaglini, and Patrick
  Salle, in Sixth Colloquium on Automata, Languages and Programming.
  Springer, pages 133--146, 1979.

* Algebras and combinators. Erwin Engeler, Algebra Universalis,
  vol. 13, pages 389-392, 1981.

* A Set-Theoretical Definition of Application. Gordon D. Plotkin,
  University of Edinburgh, Technical Report MIP-R-95, 1972.

* Set-theoretical and other elementary models of the λ-calculus.
  Gordon D. Plotkin, Theoretical Computer Science, vol. 121,
  pages 351-409, 1993.

* The Parametric Lambda Calculus. Simona Ronchi Della Rocca and Luca
  Paolini, Springer, 2004.

* Data Types as Lattices. Dana Scott, SIAM Journal on Computing,
  vol. 5, pages 522-587, 1976.

## Unicode

This chapter uses the following unicode:

    ⊥  U+22A5  UP TACK (\bot)
    ↦  U+21A6  RIGHTWARDS ARROW FROM BAR (\mapsto)
    ⊔  U+2294  SQUARE CUP (\lub)
    ⊑  U+2291  SQUARE IMAGE OF OR EQUAL TO (\sqsubseteq)
    ⨆ U+2A06  N-ARY SQUARE UNION OPERATOR (\Lub)
    ⊢  U+22A2  RIGHT TACK (\|- or \vdash)
    ↓  U+2193  DOWNWARDS ARROW (\d)
    ᶜ  U+1D9C  MODIFIER LETTER SMALL C (\^c)
    ℰ  U+2130  SCRIPT CAPITAL E (\McE)
    ≃  U+2243  ASYMPTOTICALLY EQUAL TO (\~- or \simeq)
    ∈  U+2208  ELEMENT OF (\in)
    ⊆  U+2286  SUBSET OF OR EQUAL TO (\sub= or \subseteq)
