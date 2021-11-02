{-# OPTIONS --without-K --exact-split #-}
-- Note we've removed the "safe" tag so that we can postulate function extensionality

module exercises7 where
{-
Please rename your file to exercises7-yourusername.agda
-}

open import Agda.Primitive public
{-
open means we can access all definitions in Agda.Primitive
public means any file that imports this one gets Agda.Primitive too.
-}

UU : (i : Level) → Set (lsuc i)
UU i = Set i

-- The one-sided identity type is the type family
data Id {i : Level}{A : UU i}(a : A) : A → UU i where
    refl : Id a a

-- The transport function 
tr : {i j : Level}{A : UU i}(B : A → UU j){x y : A} → (Id x y) → (B x) → (B y)
tr B refl b = b

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
-- The underscore in (x : _) is a reference to the implicit argument A.
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

is-contr : {i : Level}(A : UU i) → UU i
is-contr A = Σ A (λ a → ((x : A) → Id a x))

_≃_ : {i j : Level}(A : UU i)(B : UU j) → UU (i ⊔ j)
A ≃ B = Σ (A → B)(λ f → is-equiv f)

-- a fiberwise version of is-equiv for families of maps
is-fiberwise-equiv : {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} → ((x : A) → B x → C x) → UU (i ⊔ (j ⊔ k))
is-fiberwise-equiv f = (x : _) → is-equiv (f x)

-- Exercise: define htpy-eq, converting identifications between functions to homotopies
-- htpy-eq : {i j : Level}{A : UU i}{B : A → UU j}{f g : (a : A) → B a} → (Id f g) → (f ∼ g)

-- Function extensionality postulates that htpy-eq is an equivalence
-- FUNEXT : {i j : Level}{A : UU i}{B : A → UU j} → (f : (x : A) → B x) → UU (i ⊔ j)
-- FUNEXT f = is-fiberwise-equiv λ g → htpy-eq {f = f}{g = g}
-- After solving the previous exercise, uncomment the definition of FUNEXT above.

-- Exercise: define the type that states the weak function extensionality axiom
-- WARNING: be careful with parentheses!
-- WEAK-FUNEXT : {i j : Level}(A : UU i)(B : A → UU j) → UU (i ⊔ j) 

-- From now on we will be assuming that function extensionality hold; "postulate" requires removing the "safe" flag
-- Uncomment the following line after you've defined "htpy-eq" and uncommented "FUNEXT"
-- postulate funext : {i j : Level} {A : UU i} {B : A → UU j} (f : (x : A) → B x) → FUNEXT f

-- Exercise: assuming funext, prove that
-- the identity type Id f g in a function type is equivalent to the type f ∼ g of homotopies
-- Hint: type "equiv-funext {f = f}{g = g} = ?" to bring f and g into scope
-- equiv-funext : {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x} → (Id f g) ≃ (f ∼ g)

-- Exercise: define eq-htpy, the inverse map to htpy-eq

-- The next series of exercises aim to use function extensionality to prove the dependent universal property of the unit type 𝟙:
data 𝟙 : UU lzero where 
    star : 𝟙

-- Exercise: given a type family P over 𝟙 define the map "ev-star" that evaluates at the term star
-- ev-star : {i : Level}(P : 𝟙 → UU i) → ((x : 𝟙) → P x) → P star

-- Exercise: use the induction principle for unit types to define an inverse function
-- ind-unit : {i : Level}(P : 𝟙 → UU i) → P star → ((x : 𝟙) → P x)

-- Exercise: define a homotopy (ev-star P ∘ ind-unit P) ∼ id (P star)
-- is-section-ev-star-ind-unit : {i : Level}(P : 𝟙 → UU i) → (ev-star P ∘ ind-unit P) ∼ id (P star)

-- Exercise: define a homotopy (ind-unit P ∘ ev-star P) ∼ id ((x : 𝟙) → P x)
-- Hint: eq-htpy can be used to define identifications between functions
-- Hint: if you want to use induction afterwards type "eq-htpy λ {star → ?}"
-- is-retraction-ind-unit-ev-star : {i : Level}(P : 𝟙 → UU i) → (ind-unit P ∘ ev-star P) ∼ id ((x : 𝟙) → P x)

-- Challenge Exercise: prove the dependent universal property of the unit type, showing that for any family 
-- P : 𝟙 → UU i, ev-star P is an equivalence
-- dependent-universal-property-unit : {i : Level}(P : 𝟙 → UU i) → is-equiv (ev-star P)

-- Challenge Exercise: define the (homotopy) fiber "fib f b" for f : A → B and b : B
-- Hint: write "fib {blah = blah} f y = ?" to bring "blah" into scope
-- fib : {i j : Level}{A : UU i}{B : UU j} → (A → B) → B → UU (i ⊔ j)

-- The next series of exercises will show that for a type family B over
-- A and a : A the strict fiber B a is equivalent to the homotopy fiber of pr1 : Σ A B → A
-- Rather than writing "{i j : Level}{A : UU i}{B : A → UU j}{a : A} →" at the start of each type declaration
-- we're packaging this information into an unnamed module (hence the underscore). Note the indentation in what follows.
module _ {i j : Level}{A : UU i}{B : A → UU j}{a : A} where

    -- Challenge Exercise: for any type family B over A and any a : A define a map B a → fib pr1 a
    -- htpy-fib-strict-fib : B a → fib {i ⊔ j}{i}{Σ A B}{A} pr1 a
    
    -- Challenge Exercise: for any type family B over A and any a : A define a map fib pr1 a → B a
    -- strict-fib-htpy-fib : fib {i ⊔ j}{i}{Σ A B}{A} pr1 a → B a
    
    -- Challenge Exercise: prove these maps are inverses up to homotopy
    -- Optional Exercise: come up with better names for these homotopies
    -- retract-htpy : (strict-fib-htpy-fib ∘ htpy-fib-strict-fib) ∼ id (B a)
    
    -- other-htpy : (htpy-fib-strict-fib ∘ strict-fib-htpy-fib) ∼ id (fib {i ⊔ j}{i}{Σ A B}{A} pr1 a)
    
    -- Challenge Exercise: prove the lemma we keep using:
    -- the-lemma-we-keep-using : (B a) ≃ (fib {i ⊔ j}{i}{Σ A B}{A} pr1 a)
    