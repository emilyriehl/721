{-# OPTIONS --without-K --exact-split --safe #-}

module exercises2 where
{-
Please rename your file to exercises2-yourusername.agda
-}

open import Agda.Primitive public
{-
open means we can access all definitions in Agda.Primitive
public means any file that imports this one gets Agda.Primitive too.
-}

UU : (i : Level) → Set (lsuc i)
UU i = Set i

data ℕ : UU lzero where
    zero-ℕ : ℕ
    succ-ℕ : ℕ → ℕ

-- Recall ℕ is an example of an inductive type. The unit type is another example:
data unit : UU lzero where
    star : unit

-- Here you've told agda that the unit type is a type in "UU lzero" with one constructor "star : unit".
-- When you apply "pattern matching" (C-c C-c) to define a function (f : (x : unit) → P x) you're appealing to the elimination rule
-- for the inductive type "unit", which agda automatically knows about. But you can also express the elimination rule by defining a function ind-unit as follows:

ind-unit : {i : Level}{P : unit → UU i} → P star → ((x : unit) → P x)
ind-unit q star = q

-- Exercise 4.2: define an inductive type bool (in UU lzero) that comes with two terms true and false

-- Exercise 4.2.a: construct boolean negation neg-bool : bool → bool

-- Exercise 4.2.b: construct boolean conjuction _∧_ : bool → bool → bool
-- type "\and" for "∧"

-- Exercise 4.2.c: construct boolean disjunction _∨_ : bool → bool → bool
-- type "\or" for "∨"

-- Exercise 4.2: define a function ind-bool in context {i : Level}{P : (t : bool) → UU i} that gives boolean induction

-- type "\sqcup" for "⊔". This is a union of universe levels defined in Agda.Primitive
data coprod {i j : Level}(A : UU i)(B : UU j) : UU (i ⊔ j) where
    inl : A → coprod A B
    inr : B → coprod A B

ℤ : UU lzero
ℤ = coprod ℕ (coprod unit ℕ)

in-neg : ℕ → ℤ
in-neg n = inl n

in-pos : ℕ → ℤ
in-pos n = inr (inr n)

neg-one-ℤ : ℤ
neg-one-ℤ = in-neg zero-ℕ

zero-ℤ : ℤ
zero-ℤ = inr (inl star)

one-ℤ : ℤ
one-ℤ = in-pos zero-ℕ

-- Exercise 4.1.a: define the predecessor function pred-ℤ : ℤ → ℤ

-- Exercise 4.1.b: define the negation function neg-ℤ : ℤ → ℤ

-- Exercise: define succ-ℤ : ℤ → ℤ

-- Challenge Exercise 4.1.b/c: define add-ℤ and/or mul-ℤ
-- Can you do it without relying on any functions on ℕ?

-- type "\Sigma" for "Σ"
data Σ {i j : Level}(A : UU i)(B : A → UU j) : UU(i ⊔ j) where
    pair : (x : A) → B x → Σ A B

-- Exercise: define pr1 and pr2 in the context of {i j : Level}{A : UU i}{B : A → UU j}

-- It is convenient to have special notation for product types.
-- Alternatively, _×_ could be defined as a data type with constructor pair' : A → B → A × B
_×_ : {i j : Level}(A : UU i)(B : UU j) → UU (i ⊔ j)
A × B = Σ A (λ x → B)

data empty : UU lzero where

¬_ : {i : Level} → UU i → UU i
¬ A = A → empty

-- Exercise: delete the second line in the definition of the ex-falsp function and try to get agda to re-generate it for you
ex-falso : {i : Level}{A : UU i} → empty → A
ex-falso () 

-- Exercise: define the contrapositive proving that P implies Q implies that not P implies not Q

-- Solve the following exercises in the context of {i : Level}{P : UU i}

-- Exercise 4.3.b: define intro-dn, proving that P implies ¬ ¬ P

-- Exercise 4.3.a: define law-non-contradiction, a term that proves that P and ¬ P cannot both be true

-- Challenge Exercise 4.3.e: define dn-elim-neg, proving that ¬ ¬ ¬ P → ¬ P 

-- Exercise: define lem-dn-elim, proving that that law of excluded middle implies double negation elimination
-- lem-dn-elim : {i : Level}{P : UU i} → coprod P (¬ P) → (¬ ¬ P → P)

-- Challenge Exercise: define nn-lem, proving that the law of excluded middle is not false

-- Challenge Exercise 4.3.c: prove that double negation elimination is not false by defining dn-dn-elim : ¬ ¬ (¬ ¬ P → P)

-- Challenge Exercise: define dn-elim-lem, proving that if double negation elimination holds for all types P then lem holds for all types Q



