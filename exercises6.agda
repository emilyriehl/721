{-# OPTIONS --without-K --exact-split --safe #-}

module exercises6 where
{-
Please rename your file to exercises6-yourusername.agda
-}

open import Agda.Primitive public
{-
open means we can access all definitions in Agda.Primitive
public means any file that imports this one gets Agda.Primitive too.
-}

UU : (i : Level) → Set (lsuc i)
UU i = Set i

-- The one-sided identity type is the type family in context of a type A and term a : A freely generated by refl_a : Id a a.
data Id {i : Level}{A : UU i}(a : A) : A → UU i where
    refl : Id a a

-- Definition 5.2.2: define "inv", the function that reverses paths
inv : {i : Level}{A : UU i}{x y : A} → (Id x y) → (Id y x)
inv refl = refl

_·_ : {i : Level}{A : UU i}{x y z : A} → (Id x y) → (Id y z) → (Id x z)
refl · q = q

-- Definition 5.3.1: the application of functions on paths
ap : {i j : Level}{A : UU i}{B : UU j}{x y : A} → (f : A → B) → (Id x y) → (Id (f x) (f y))
ap f refl = refl

-- The transport function 
tr : {i j : Level}{A : UU i}(B : A → UU j){x y : A} → (Id x y) → (B x) → (B y)
tr B refl b = b

-- Definition 9.1.2: the type of homotopies "f ∼ g" for a pair of dependent functions; type "\sim" for "∼"
-- The underscore in (x : _) is a reference to the implicit argument A.
_∼_ : {i j : Level}{A : UU i}{B : A → UU j} → (f g : (a : A) → B a) → UU(i ⊔ j)
f ∼ g = (x : _) → Id (f x) (g x)

_∘_ : {i j k : Level} {A : UU i} {B : UU j} {C : UU k} → (B → C) → (A → B) → (A → C)
(g ∘ f) a = g (f a)

-- Exercise: construct the whiskering operations on homotopies between non-dependent functions
-- _·r_ : {i j k : Level}{A : UU i}{B : UU j}{C : UU k} {f g : B → C} → (f ∼ g) → (h : A → B) → ((f ∘ h) ∼ (g ∘ h))

-- _·l_ : {i j k : Level}{A : UU i}{B : UU j}{C : UU k} {f g : A → B} → (h : B → C) → (f ∼ g) → ((h ∘ f) ∼ (h ∘ g))

-- Exercise: define the concatenation of homotopies
-- concat-htpy : {i j : Level}{A : UU i}{B : A → UU j}{f g h : (x : A) → B x} → (f ∼ g) → (g ∼ h) → (f ∼ h)

-- Preliminaries on dependent pair types; "\Sigma" for "Σ"
data Σ {i j : Level}(A : UU i)(B : A → UU j) : UU(i ⊔ j) where
    pair : (x : A) → B x → Σ A B

pr1 : {i j : Level}{A : UU i}{B : A → UU j} → Σ A B → A
pr1 (pair a b) = a    

pr2 : {i j : Level}{A : UU i}{B : A → UU j} → (z : Σ A B) → B (pr1 z) 
pr2 (pair a b) = b 

_×_ : {i j : Level}(A : UU i)(B : UU j) → UU (i ⊔ j)
A × B = Σ A (λ x → B)

-- Identities and composition; type "\circ" to get "∘"
id : {i : Level} (A : UU i) → A → A
id A a = a

-- Definition 9.2.1: equivalences as bi-invertible maps
sec : {i j : Level}{A : UU i}{B : UU j} → (A → B) → UU(i ⊔ j)
sec {A = A}{B = B} f = Σ (B → A) λ s → (f ∘ s) ∼ id B

retr : {i j : Level}{A : UU i}{B : UU j} → (A → B) → UU(i ⊔ j)
retr {A = A}{B = B} f = Σ (B → A) λ r → (r ∘ f) ∼ id A

is-equiv : {i j : Level}{A : UU i}{B : UU j} → (A → B) → UU(i ⊔ j)
is-equiv f = (sec f) × (retr f)

-- The type of equivalences between A and B; type "\simeq" for "≃".
_≃_ : {i j : Level} → (A : UU i) → (B : UU j) → UU(i ⊔ j)
A ≃ B = Σ (A → B)(λ f → is-equiv f)

is-contr : {i : Level} → (A : UU i) → UU i
is-contr A = Σ A (λ a → ((x : A) → Id a x))

-- Exercise: show that if A ≃ B and B is contractible then A is contractible
-- is-contr-equiv-contr : {i j : Level}{A : UU i}{B : UU j} → (A ≃ B) → is-contr B → is-contr A

-- Exercise: show that any function between contractible types is an equivalence
-- is-equiv-is-contr : {i j : Level} {A : UU i}{B : UU j} → (is-contr A) → (is-contr B) → (f : A → B) → is-equiv f

-- Section 12.3 general truncation levels
data 𝕋 : UU lzero where
  neg-two-𝕋 : 𝕋
  succ-𝕋 : 𝕋 → 𝕋

-- Exercise: define is-trunc, a function which takes a truncation level k : 𝕋 and a type A to the type is-trunc k A

-- Exercise: define is-prop using is-trunc

-- Challenge Exercise 10.1 from the previous assignment defines is-prop-is-contr below using eq-is-contr and left-inv  
eq-is-contr : {i : Level}{A : UU i} → is-contr A → (x y : A) → (Id x y)
eq-is-contr (pair c h) x y = (inv (h x)) · h y

left-inv : {i : Level}{A : UU i}{x y : A} → (p : Id x y) → Id ((inv p) · p) refl
left-inv refl = refl

-- This is commented out because is-prop has not yet been defined
-- Once you solve the previous exercise (and define is-prop) uncomment the next two lines because you'll need it very soon
-- is-prop-is-contr : {i : Level}{A : UU i} → (is-contr A) → (is-prop A)
-- is-prop-is-contr (pair c h) x y = pair (eq-is-contr (pair c h) x y) (λ { refl → left-inv (h x) } ) 

-- Exercise (Proposition 12.4.3): prove if A is k-truncated then A is k+1-truncated
-- is-trunc-succ-is-trunc : {i : Level}{A : UU i}(k : 𝕋) → is-trunc k A → is-trunc (succ-𝕋 k) A

-- The aim of the next series of exercises is to prove a logical equivalence between
-- is-prop, all-elements-equal, and is-proof-irrelevant
all-elements-equal : {i : Level} → UU i → UU i
all-elements-equal A = (x y : A) → (Id x y)

is-proof-irrelevant : {i : Level} → UU i → UU i
is-proof-irrelevant A = A → is-contr A

-- Exercise: prove that is-prop implies all-elements-equal
-- all-elements-equal-is-prop : {i : Level} {A : UU i} → is-prop A → all-elements-equal A

-- Exercise: prove that all-elements-equal implies is-proof-irrelevant
-- is-proof-irrelevant-all-elements-equal : {i : Level}{A : UU i} → all-elements-equal A → is-proof-irrelevant A

-- Challenge Exercise: prove that is-proof-irrelevant implies is-prop
-- is-prop-is-proof-irrelevant : {i : Level}{A : UU i} → is-proof-irrelevant A → is-prop A

-- type "\sqcup" for "⊔". This is a union of universe levels defined in Agda.Primitive
data coprod {i j : Level}(A : UU i)(B : UU j) : UU (i ⊔ j) where
    inl : A → coprod A B
    inr : B → coprod A B

data ∅ : UU lzero where

¬_ : {i : Level} → UU i → UU i
¬ A = A → ∅

data 𝟙 : UU lzero where
    star : 𝟙

-- Challenge Exercise 12.4(a): Show that if A and B are contractible types then A + B is not contractible
-- Hint: transport in a suitably defined type family can help produce a term of type ∅ 
-- is-not-contr-coprod-is-contr : {i j : Level}{A : UU i}{B : UU j} → is-contr A → is-contr B → ¬ (is-contr (coprod A B))