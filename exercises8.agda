{-# OPTIONS --without-K --exact-split #-}
-- Note we've removed the "safe" tag so that we can postulate univalence

module exercises8 where
{-
Please rename your file to exercises8-yourusername.agda
-}

open import Agda.Primitive public

UU : (i : Level) → Set (lsuc i)
UU i = Set i

-- The one-sided identity type is the type family
data Id {i : Level}{A : UU i}(a : A) : A → UU i where
    refl : Id a a

-- The dependent pair type
data Σ {i j : Level}(A : UU i)(B : A → UU j) : UU(i ⊔ j) where
    pair : (x : A) → B x → Σ A B

pr1 : {i j : Level}{A : UU i}{B : A → UU j} → Σ A B → A
pr1 (pair a b) = a 

pr2 : {i j : Level}{A : UU i}{B : A → UU j} → (z : Σ A B) → B (pr1 z)
pr2 (pair a b) = b 

_×_ : {i j : Level}(A : UU i)(B : UU j) → UU (i ⊔ j)
A × B = Σ A (λ x → B)

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

_≃_ : {i j : Level}(A : UU i)(B : UU j) → UU (i ⊔ j)
A ≃ B = Σ (A → B)(λ f → is-equiv f)

-- Exercise: define the identity equivalence
-- id-equiv : {i : Level}{A : UU i} → A ≃ A
-- id-equiv {A = A} = 

-- Exercise: define equiv-eq : Id A B → A ≃ B for any types A B of the same universe level
-- equiv-eq : {i : Level}{A B : UU i} → Id A B → A ≃ B

-- 17.1.1: the univalence axiom asserts the existence of a term of the following type
-- after solving the previous exercises, uncomment the following
-- UNIVALENCE : {i : Level}(A B : UU i) → UU (lsuc i)
-- UNIVALENCE A B = is-equiv (equiv-eq {A = A}{B = B})

-- uncomment this as well to postulate the univalence axiom
-- postulate univalence : {i : Level}(A B : UU i) → UNIVALENCE A B

-- Exercise: use the postulated term univalence to express the univalence axiom as an equivalence 
-- between the identity type and the type of equivalences.
-- Hint: "univalence _ _" invites agda to infer the two arguments (without bringing them into scope)
-- equiv-univalence : {i : Level} {A B : UU i} → Id A B ≃ (A ≃ B)

-- Exercise: use the univalence axiom to define an inverse eq-equiv to equiv-eq
-- Hint: after declaring the type for eq-equiv, start your new line by writing 
-- "eq-equiv {A = A}{B = B} = ?" to bring the type variables into scope and open up a hole.
-- Type whatever term you guess might be relevant into that hole, but  
-- before asking agda to accept it (with C-c C-space) you can type "C-c C-d" 
-- to check what type the term you've written belongs to.
-- Eg if you type in the term "univalence" and type C-c C-d agda tells you 
-- "{i : Level} (A₁ B₁ : UU i) → UNIVALENCE A₁ B₁"
-- eq-equiv : {i : Level}{A B : UU i} → A ≃ B → Id A B
-- eq-equiv {A = A} {B = B} = ?

-- Exercise: constructions that convert types to types have the form of a function P : UU i → UU j
-- Show that any such P respects identifications between types.
-- id-invariance : {i j : Level}(P : (UU i) → (UU j)){A B : UU i} → (Id A B) → (Id (P A) (P B))

-- Exercise: using the univalence axiom, we can prove the corresponding result for equivalences between types
-- For any family of types P : UU i → UU j and any types A B : UU i, show that A ≃ B → PA ≃ P B
-- ua-equiv-invariance : {i j : Level}(P : (UU i) → (UU j)){A B : UU i} → (A ≃ B) → (P A ≃ P B)

-- Exercise: it's useful to also have proofs of the weaker result, that A ≃ B → PA → PB
-- ua-equiv-invariance-implication : {i j : Level}(P : (UU i) → (UU j)){A B : UU i} → (A ≃ B) → (P A → P B)

-- Exercise: it's also convenient to know that A ≃ B → PB → PA
-- Hint: Recall that you can type a term into a hole and then type C-c C-d to see what type it belongs 
-- before asking agda to accept it with C-c C-space
-- ua-equiv-invariance-converse : {i j : Level}(P : (UU i) → (UU j)){A B : UU i} → (A ≃ B) → (P B → P A)

-- The remaining exercises aim to illustrate the utility of ua-equiv-invariance by using it to provide 
-- short proofs of a number of results, all of which could be proven without univalence (but through long arguments)

-- Exercise: define is-prop in any of the logically equivalent ways (which you pick is up to you)

-- Exercise: prove that if A ≃ B then is-prop A ≃ is-prop B
-- Q: Does the converse hold?
-- is-prop-equiv-is-prop : {i : Level}{A B : UU i} → (A ≃ B) → (is-prop A) ≃ (is-prop B)

-- Exercise: use ua-equiv-invariance to show that function types respect equivalences in the domain variable
-- domain-function-equiv-invariance : {i j : Level}{A B : UU i}{C : UU j} → (A ≃ B) → (A → C) ≃ (B → C)

-- Exercise: use ua-equiv-invariance to show that function types respect equivalences in the codomain variable
-- codomain-function-equiv-invariance : {i j : Level}{A B : UU i}{C : UU j} → (A ≃ B) → (C → A) ≃ (C → B)

-- Challenge Exercise: use general-equiv-invariance to prove that equivalences can be composed
-- comp-equiv : {i : Level}{A B C : UU i} → (A ≃ B) → (B ≃ C) → (A ≃ C)

-- Challenge Exercise: prove the general equivalence invariance of function types
-- complete-function-equiv-invariance : {i j : Level}{A B : UU i}{C D : UU j} → (A ≃ B) → (C ≃ D) → (A → C) ≃ (B → D)

