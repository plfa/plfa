---
title     : "Inference: Bidirectional type inference"
layout    : page
permalink : /Inference
---

Given Raw terms and inherently typed terms, specify
an algorithm going from one to the other.

There are *many* ways to do this. Which is best?

First dimension: staged/direct

* Staged: Raw -> Scoped, Scoped -> Typed
* Direct: Raw -> Typed in one fell swoop

Second dimension: derivation/function

* Derviation: Type derivations similar to usual rules, erasure of typing to Typed
* Function: Function to compute Typed term directly

Let's fiddle about with a couple of these to see which is best.

The Agda manual gives a solution for Staged/Function (second half of staged).

  I'm quite keen to try Direct/Derivation.


## Imports

\begin{code}
module Inference where
\end{code}

\begin{code}
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; _≢_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; map; foldr; filter; length)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.String using (String; _≟_; _++_)
open import Data.Product
  using (_×_; proj₁; proj₂; ∃; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (¬?)
import Collections

pattern [_]       w        =  w ∷ []
pattern [_,_]     w x      =  w ∷ x ∷ []
pattern [_,_,_]   w x y    =  w ∷ x ∷ y ∷ []
pattern [_,_,_,_] w x y z  =  w ∷ x ∷ y ∷ z ∷ []
\end{code}


## Identifiers

\begin{code}
Id : Set
Id = String
\end{code}

## Syntax

\begin{code}
infix   4  _∋_`:_
infix   4  _⊢_↑_
infix   4  _⊢_↓_
infixl  5  _,_`:_
infix   5  _`:_
infixr  6  _`→_
infix   6  `λ_`→_
infix   6  `μ_`→_
infixl  9  _·_

data Type : Set where
  `ℕ   : Type
  _`→_ : Type → Type → Type

data Ctx : Set where
  ε      : Ctx
  _,_`:_ : Ctx → Id → Type → Ctx

data Term : Set where
  ⌊_⌋                        : Id → Term
  `λ_`→_                     : Id → Term → Term
  _·_                        : Term → Term → Term
  `zero                      : Term
  `suc                       : Term → Term   
  `case_[`zero`→_|`suc_`→_]  : Term → Term → Id → Term → Term
  `μ_`→_                     : Id → Term → Term
  _`:_                       : Term → Type → Term
\end{code}

## Example terms

\begin{code}
two : Term
two = `suc (`suc `zero) `: `ℕ

plus : Term
plus = (`μ "p" `→ `λ "m" `→ `λ "n" `→
          `case ⌊ "m" ⌋ [`zero`→ ⌊ "n" ⌋
                        |`suc "m" `→ `suc (⌊ "p" ⌋ · ⌊ "m" ⌋) · ⌊ "n" ⌋ ])
            `: `ℕ `→ `ℕ

four : Term
four = plus · two · two

Ch : Type
Ch = (`ℕ `→ `ℕ) `→ `ℕ `→ `ℕ

twoCh : Term
twoCh = (`λ "s" `→ `λ "z" `→ ⌊ "s" ⌋ · (⌊ "s" ⌋ · ⌊ "z" ⌋)) `: Ch

plusCh : Term
plusCh = (`λ "m" `→ `λ "n" `→ `λ "s" `→ `λ "z" `→
           ⌊ "m" ⌋ · ⌊ "s" ⌋ · (⌊ "n" ⌋ · ⌊ "s" ⌋ · ⌊ "z" ⌋))
             `: Ch `→ Ch `→ Ch

fromCh : Term
fromCh = (`λ "m" `→ ⌊ "m" ⌋ · (`λ "x" `→ `suc ⌊ "x" ⌋) · `zero)
           `: Ch `→ `ℕ

fourCh : Term
fourCh = fromCh · (plusCh · twoCh · twoCh)
\end{code}
## Bidirectional type checking

\begin{code}
data _∋_`:_ : Ctx → Id → Type → Set where

  Z : ∀ {Γ x A}
      --------------------
    → Γ , x `: A ∋ x `: A

  S : ∀ {Γ w x A B}
    → w ≢ x
    → Γ ∋ w `: B
      --------------------
    → Γ , x `: A ∋ w `: B

data _⊢_↑_ : Ctx → Term → Type → Set
data _⊢_↓_ : Ctx → Term → Type → Set

data _⊢_↑_ where

  Ax : ∀ {Γ A x}
    → Γ ∋ x `: A
      --------------
    → Γ ⊢ ⌊ x ⌋ ↑ A

  _·_ : ∀ {Γ L M A B}
    → Γ ⊢ L ↑ A `→ B
    → Γ ⊢ M ↑ A
      ---------------
    → Γ ⊢ L · M ↑ B

  ↑↓ : ∀ {Γ M A}
    → Γ ⊢ M ↓ A
      ----------------
    → Γ ⊢ M `: A ↑ A

data _⊢_↓_ where

  ⊢λ : ∀ {Γ x N A B}
    → Γ , x `: A ⊢ N ↓ B
      -----------------------
    → Γ ⊢ `λ x `→ N ↓ A `→ B

  ⊢zero : ∀ {Γ}
      ---------------
    → Γ ⊢ `zero ↓ `ℕ

  ⊢suc : ∀ {Γ M}
    → Γ ⊢ M ↓ `ℕ
      ----------------
    → Γ ⊢ `suc M ↓ `ℕ

  ⊢case : ∀ {Γ L M x N A}
    → Γ ⊢ L ↑ `ℕ
    → Γ ⊢ M ↓ A
    → Γ , x `: `ℕ ⊢ N ↓ A
      ------------------------------------------
    → Γ ⊢ `case L [`zero`→ M |`suc x `→ N ] ↓ A

  ⊢μ : ∀ {Γ x N A}
    → Γ , x `: A ⊢ N ↓ A
      -----------------------
    → Γ ⊢ `μ x `→ N ↓ A

  ↓↑ : ∀ {Γ M A}
    → Γ ⊢ M ↑ A
      ----------
    → Γ ⊢ M ↓ A
\end{code}

## Type checking monad

\begin{code}
Msg : Set
Msg = String

data TC (A : Set) : Set where
  error  : Msg → Term → List Type → TC A
  return : A → TC A

_>>=_ : ∀ {A B : Set} → TC A → (A → TC B) → TC B
error msg M As >>= k  =  error msg M As
return v       >>= k  =  k v
\end{code}

## Type inferencer

\begin{code}
_≟Tp_ : (A B : Type) → Dec (A ≡ B)
A ≟Tp B = {!!}

data Lookup (Γ : Ctx) (x : Id) : Set where
  ok : ∀ (A : Type) → (Γ ∋ x `: A) → Lookup Γ x

lookup : ∀ (Γ : Ctx) (x : Id) → TC (Lookup Γ x)
lookup ε x  =
  error "variable not bound" ⌊ x ⌋ []
lookup (Γ , x `: A) w with w ≟ x
... | yes refl =
  return (ok A Z)
... | no w≢ =
  do ok A ⊢x ← lookup Γ w
     return (ok A (S w≢ ⊢x))
  
data Synthesize (Γ : Ctx) (M : Term) : Set where
  ok : ∀ (A : Type) → (Γ ⊢ M ↑ A) → Synthesize Γ M

synthesize : ∀ (Γ : Ctx) (M : Term) → TC (Synthesize Γ M)
inherit : ∀ (Γ : Ctx) (M : Term) (A : Type) → TC (Γ ⊢ M ↓ A)

synthesize Γ ⌊ x ⌋ =
  do ok A ⊢x ← lookup Γ x
     return (ok A (Ax ⊢x))
synthesize Γ (L · M) =
  do ok (A₀ `→ B) ⊢L ← synthesize Γ L
       where ok `ℕ _ → error "must apply function" (L · M) []
     ok A₁ ⊢M ← synthesize Γ M
     yes refl ← return (A₀ ≟Tp A₁)
       where no _ → error "types differ in application" (L · M) [ A₀ , A₁ ]
     return (ok B (⊢L · ⊢M))
synthesize Γ (M `: A) =
  do ⊢M ← inherit Γ M A
     return (ok A (↑↓ ⊢M))
{-# CATCHALL #-}
synthesize Γ M =
  error "cannot synthesize type for term" M []

inherit Γ (`λ x `→ N) (A `→ B) =
  do ⊢N ← inherit (Γ , x `: A) N B
     return (⊢λ ⊢N)
inherit Γ (`λ x `→ N) `ℕ =
  error "lambda cannot be natural" (`λ x `→ N) []
inherit Γ `zero `ℕ =
  return ⊢zero
inherit Γ `zero (A `→ B) =
  error "zero cannot be function" `zero [ A `→ B ]
inherit Γ (`suc M) `ℕ =
  do ⊢M ← inherit Γ M `ℕ
     return (⊢suc ⊢M)
inherit Γ (`suc M) (A `→ B) =
  error "suc cannot be function" (`suc M) [ A `→ B ]
inherit Γ `case L [`zero`→ M |`suc x `→ N ] A =
  do ok `ℕ ⊢L ← synthesize Γ L
       where ok (A `→ B) _ → error "cannot case on function"
                                   (`case L [`zero`→ M |`suc x `→ N ])
                                   [ A `→ B ]
     ⊢M ← inherit Γ M A
     ⊢N ← inherit (Γ , x `: `ℕ) N A
     return (⊢case ⊢L ⊢M ⊢N)
inherit Γ (`μ x `→ M) A =
  do ⊢M ← inherit (Γ , x `: A) M A
     return (⊢μ ⊢M)
{-# CATCHALL #-}
inherit Γ M A₀ =
  do ok A₁ ⊢M ← synthesize Γ M
     yes refl ← return (A₀ ≟Tp A₁)
       where no _ → error "inheritance and synthesis conflict" M [ A₀ , A₁ ]
     return (↓↑ ⊢M)
\end{code}

