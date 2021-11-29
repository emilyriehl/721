{-# OPTIONS --without-K --exact-split #-}
-- Note we've removed the "safe" tag so that we can postulate everything

module exercises10 where
{-
Please rename your file to exercises10-yourusername.agda
-}

open import Agda.Primitive public

UU : (i : Level) → Set (lsuc i)
UU i = Set i

-- The one-sided identity type is the type family
data Id {i : Level}{A : UU i}(a : A) : A → UU i where
    refl : Id a a

-- Exercise: uncomment the following code and note that agda doesn't like it
-- data 𝕊¹ : UU lzero where
--     base : 𝕊¹
--     loop : Id base base
-- In other words, agda doesn't natively support higher inductive types, so we'll instead have to postulate 
-- everything we'd like to know about 𝕊¹.

-- type "\bS\^1" for "𝕊¹"
postulate 𝕊¹ : UU lzero

postulate base-𝕊¹ : 𝕊¹

postulate loop-𝕊¹ : Id base-𝕊¹ base-𝕊¹

-- Since we haven't defined 𝕊¹ to be any sort of inductive type we don't have the elimination and computation rules
-- associated to 𝕊¹. We must first define the types that state these and then postulate proofs.
-- For simplicity, we'll only discuss the non-dependent universal property of the circle.

-- The dependent pair type
data Σ {i j : Level}(A : UU i)(B : A → UU j) : UU(i ⊔ j) where
    pair : (x : A) → B x → Σ A B

_×_ : {i j : Level}(A : UU i)(B : UU j) → UU (i ⊔ j)
A × B = Σ A (λ x → B)

pr1 : {i j : Level}{A : UU i}{B : A → UU j} → Σ A B → A
pr1 (pair a b) = a 

pr2 : {i j : Level}{A : UU i}{B : A → UU j} → (z : Σ A B) → B (pr1 z)
pr2 (pair a b) = b 

-- Exercise: for a type X define a type "free-loops X" that consists of pairs given by an x : X and a loop p : x = x
-- Its terms are "free loops" in X, meaning loops on any base point.
-- free-loops : {i : Level} → (X : UU i) → UU i

-- Exercise: define a function constant-loops that takes a point in X to the constant loop at that point
-- constant-loops : {i : Level} {X : UU i} → X → free-loops X

-- Exercise: define base-free-loops : (free-loops X) → X projecting from a free loop to its base point
-- base-free-loops : {i : Level} {X : UU i} → free-loops X → X

-- Exercise: define loop-free-loops, a dependent function that sends a free loop to the loop at its base point
-- loop-free-loops : {i : Level} {X : UU i} → (p : free-loops X) → Id (base-free-loops p) (base-free-loops p)

-- Concatenation and inversion of paths
_·_ : {i : Level}{A : UU i}{x y z : A} → (Id x y) → (Id y z) → (Id x z)
refl · q = q

inv : {i : Level}{A : UU i}{x y : A} → Id x y → Id y x
inv refl = refl

data ℕ : UU lzero where
    zero-ℕ : ℕ
    succ-ℕ : ℕ → ℕ

-- Challenge Exercise: for each n : ℕ, define "n fold-loop", a function that sends a loop p at x to the loop given by 
-- the n-fold concatenation of p with itself. 
-- First, try to define this function directly. If agda complains that some identification does not hold judgmentally
-- the auxiliary function "n th loop" might help.
-- _th-loop_ : {i : Level}{X : UU i} → ℕ → (p : free-loops X) → Id (base-free-loops p) (base-free-loops p)

-- _fold-loop_ : {i : Level}{X : UU i} → ℕ → free-loops X → free-loops X
-- n fold-loop p = ?

-- Exercise: use the postulates to define a canonical term free-loop-𝕊¹ : free-loops 𝕊¹
-- free-loop-𝕊¹ : free-loops 𝕊¹

-- Definition 5.3.1: the application of functions on paths
ap : {i j : Level}{A : UU i}{B : UU j}{x y : A} → (f : A → B) → (Id x y) → (Id (f x) (f y))
ap f refl = refl

-- Exercise: define ev-free-loop : (𝕊¹ → X) → free-loops X that evaluates a function on the canonical free loop
-- ev-free-loop : {i : Level}{X : UU i} → (𝕊¹ → X) → free-loops X

-- Definition 9.1.2: the type of homotopies "f ∼ g" for a pair of dependent functions; type "\sim" for "∼"
_∼_ : {i j : Level}{A : UU i}{B : A → UU j} → (f g : (a : A) → B a) → UU(i ⊔ j)
f ∼ g = (x : _) → Id (f x) (g x)

-- function composition and identity
_∘_ : {i j k : Level}{A : UU i}{B : UU j}{C : UU k} → (B → C) → (A → B) → (A → C)
g ∘ f = λ x → g (f x)

id : {i : Level}(A : UU i) → A → A
id A a = a

-- equivalences and contractible types
sec : {i j : Level}{A : UU i}{B : UU j} → (A → B) → UU(i ⊔ j)
sec {A = A}{B = B} f = Σ (B → A) λ s → (f ∘ s) ∼ id B

retr : {i j : Level}{A : UU i}{B : UU j} → (A → B) → UU(i ⊔ j)
retr {A = A}{B = B} f = Σ (B → A) λ r → (r ∘ f) ∼ id A

is-equiv : {i j : Level}{A : UU i}{B : UU j} → (A → B) → UU(i ⊔ j)
is-equiv f = (sec f) × (retr f)

-- The non-dependent induction principle for 𝕊¹ postulates the existence of a section for ev-free-loop
-- Uncomment this after you've defined the function ev-free-loop
-- postulate 𝕊¹-induction : {i : Level}{X : UU i} → sec (ev-free-loop {X = X})

-- Exercise: from the postulate 𝕊¹-induction define ind-𝕊¹, the section to ev-free-loop
-- ind-𝕊¹ : {i : Level}{X : UU i} → free-loops X → (𝕊¹ → X)

-- Exercise: from the postulate 𝕊¹-induction define comp-𝕊¹, the homotopy
-- comp-𝕊¹ : {i : Level}{X : UU i} → (ev-free-loop ∘ ind-𝕊¹) ∼ id (free-loops X)

-- For a pair (x : X, p : x = x) in free-loops X, "comp-𝕊¹ (pair x p): is an identification in the Σ-type free-loops X
-- It will be more useful to extract a pair of paths from this single path, for which we use the function defined 
-- on exercises9.

-- Definition 5.4.1: the transport function
tr : {i j : Level}{A : UU i}(B : A → UU j){x y : A} → (Id x y) → (B x) → (B y)
tr B refl b = b

-- The identity type of Σ types are equivalent to a type "pair-of-paths" given by 
-- a path p : a = a' in A and a path q : (tr B p b) = b' in B(a').
pair-of-paths : {i j : Level}{A : UU i}{B : A → UU j} → (x y : Σ A B) → UU (i ⊔ j)
pair-of-paths (pair a b) (pair a' b') = Σ (Id a a') λ p → Id (tr _ p b) b'

-- The function that converts a path in the identity type of Σ A B into a pair of paths
pair-of-paths-path-Σ : {i j : Level}{A : UU i}{B : A → UU j} → (x y : Σ A B) → Id x y → pair-of-paths x y
pair-of-paths-path-Σ (pair x x₁) .(pair x x₁) refl = pair refl refl

-- Challenge Exercise: define base-comp-𝕊¹, the base path from comp-𝕊¹ associated to (pair x p) : free-loops X
-- base-comp-𝕊¹ : {i : Level}{X : UU i} → (l : free-loops X) → Id ((ind-𝕊¹ l) base-𝕊¹) (base-free-loops l)

-- Challenge Exercise: define loop-comp-𝕊¹, the path of loops from comp-𝕊¹ associated to (pair x p) : free-loops X
-- loop-comp-𝕊¹ : {i : Level}{X : UU i} → (l : free-loops X) 
--         → Id (tr (λ z → Id z z) (base-comp-𝕊¹ l) (ap (ind-𝕊¹ l) loop-𝕊¹)) (loop-free-loops l)

-- If we had developed the dependent induction principle for 𝕊¹ the terms ind-𝕊¹ and comp-𝕊¹ would be enough
-- to prove that ev-free-loop is an equivalence. Since we're doing the non-dependent version, we really should 
-- have postulated that ev-free-loop is an equivalence.

-- We conclude with some applications of ind-𝕊¹.

-- Exercise: define a "degree-two" function from 𝕊¹ to 𝕊¹ that sends base-𝕊¹ to base-𝕊¹ and 
-- loop-𝕊¹ to loop-𝕊¹ · loop-𝕊¹.
-- deg-two : 𝕊¹ → 𝕊¹

-- Challenge Exercise: for any n : ℕ, define a "degree n" function from 𝕊¹ to 𝕊¹ that sends base-𝕊¹ to base-𝕊¹ and -- loop-𝕊¹ to the n-fold concatentation of loop-𝕊¹ with itself
-- deg : ℕ → 𝕊¹ → 𝕊¹

-- Challenge Exercise: extend the previously-defined degree function from ℕ to ℤ by sending a negative integer -n
-- to the function that sends loop-𝕊¹ to the n-fold concantenation of the reverse of loop-𝕊¹ with itself
-- Since we don't have the unit type or coproduct types, we just define the integers directly:

data ℤ : UU lzero where
    zero-ℤ : ℤ
    pos-ℤ : ℕ → ℤ -- inclusion of the positive integers
    neg-ℤ : ℕ → ℤ -- inclusion of the negative integers

-- degree : ℤ → 𝕊¹ → 𝕊¹

