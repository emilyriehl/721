{-# OPTIONS --without-K --exact-split #-}
-- Note we've removed the "safe" tag so that we can postulate univalence

module exercises9 where
{-
Please rename your file to exercises9-yourusername.agda
-}

open import Agda.Primitive public

UU : (i : Level) → Set (lsuc i)
UU i = Set i

-- The one-sided identity type is the type family
data Id {i : Level}{A : UU i}(a : A) : A → UU i where
    refl : Id a a

-- Concatenation and inversion of paths
_·_ : {i : Level}{A : UU i}{x y z : A} → (Id x y) → (Id y z) → (Id x z)
refl · q = q

inv : {i : Level}{A : UU i}{x y : A} → Id x y → Id y x
inv refl = refl

-- The dependent pair type
data Σ {i j : Level}(A : UU i)(B : A → UU j) : UU(i ⊔ j) where
    pair : (x : A) → B x → Σ A B

pr1 : {i j : Level}{A : UU i}{B : A → UU j} → Σ A B → A
pr1 (pair a b) = a 

pr2 : {i j : Level}{A : UU i}{B : A → UU j} → (z : Σ A B) → B (pr1 z)
pr2 (pair a b) = b 

_×_ : {i j : Level}(A : UU i)(B : UU j) → UU (i ⊔ j)
A × B = Σ A (λ x → B)

-- Definition 5.3.1: the application of functions on paths
ap : {i j : Level}{A : UU i}{B : UU j}{x y : A} → (f : A → B) → (Id x y) → (Id (f x) (f y))
ap f refl = refl

-- Definition 5.4.1: the transport function
tr : {i j : Level}{A : UU i}(B : A → UU j){x y : A} → (Id x y) → (B x) → (B y)
tr B refl b = b

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

-- Exercise: define htpy-eq, converting identifications between functions to homotopies
refl-htpy : {i j : Level}{A : UU i}{B : A → UU j}{f : (a : A) → B a} → f ∼ f
refl-htpy = λ x → refl

htpy-eq : {i j : Level}{A : UU i}{B : A → UU j}{f g : (a : A) → B a} → (Id f g) → (f ∼ g)
htpy-eq refl = refl-htpy

-- function extensionality postulates that htpy-eq is an equivalence
-- Exercise: read the definitions of FUNEXT, funext, and eq-htpy and compare them with the ones from exercises7
FUNEXT : {i j : Level}{A : UU i}{B : A → UU j} (f g : (x : A) → B x) → UU (i ⊔ j)
FUNEXT f g = is-equiv (htpy-eq {f = f} {g = g})

postulate funext : {i j : Level} {A : UU i} {B : A → UU j} (f g : (x : A) → B x) → FUNEXT f g

eq-htpy : {i j : Level}{A : UU i}{B : A → UU j}{f g : (a : A) → B a} → (f ∼ g) → Id f g
eq-htpy {f = f} {g = g} = pr1 ( pr1 (funext f g))

-- For simplicity, we use the following definition of is-prop
is-prop : {i : Level}(A : UU i) → UU i
is-prop A = (x y : A) → Id x y

-- Exercise: use function extensionality to prove that a product of propositions is a proposition; here "\Pi" gives "Π"
-- Π-prop-weak-funext : {i j : Level}{A : UU i}{B : A → UU j} → ((x : A) → is-prop (B x)) → is-prop ((x : A) → B x)

-- The following series of exercises use the encode-decode method to characterize the identity type of Σ types
-- as a type "pair-of-paths" given by a path p : a = a' in A and a path q : (tr B p b) = b' in B(a').
pair-of-paths : {i j : Level}{A : UU i}{B : A → UU j} → (x y : Σ A B) → UU (i ⊔ j)
pair-of-paths (pair a b) (pair a' b') = Σ (Id a a') λ p → Id (tr _ p b) b'

-- Exercise: define a function that converts a pair of paths into a path in the identity type of Σ A B
-- path-Σ-pair-of-paths : {i j : Level}{A : UU i}{B : A → UU j} → (x y : Σ A B) → pair-of-paths x y → Id x y
-- path-Σ-pair-of-paths {B = B} 

-- Exercise: define a function that converts a path in the identity type of Σ A B into a pair of paths
-- pair-of-paths-path-Σ : {i j : Level}{A : UU i}{B : A → UU j} → (x y : Σ A B) → Id x y → pair-of-paths x y

-- Challenge Exercise: we won't actually need to know that (pair of paths x y) ≃ (Id x y) but if you'd like
-- define the missing homotopies and then use them to prove this
-- pair-of-paths-equiv : {i j : Level}{A : UU i}{B : A → UU j} → (x y : Σ A B) → (pair-of-paths x y) ≃ (Id x y)

-- Exercise: prove that the product of two propositions is a proposition
-- prod-prop : {i j : Level}{A : UU i}{B : UU j} → is-prop A → is-prop B → is-prop (A × B)

-- Exercise: show that if P is a family of propositions over A then to define a path from (a,b) to (a',b') in Σ A P
-- it suffices to define a path p : a = a' in A.
-- subtype-path-lemma : {i j : Level} {A : UU i}{P : A → UU j}(pf : (x : A) → is-prop (P x)) → (x y : Σ A P) → (Id (pr1 x) (pr1 y)) → Id x y

-- We use our simplified definition of is-prop to define is-set
is-set : {i : Level}(A : UU i) → UU i
is-set A = (x y : A) → is-prop (Id x y)

-- Egbert defines the type of semigroups as an iterated Σ-type. A semigroup is a type - called the "carrier" -
-- together with a proof that the carrier type is a set, a binary operation on the carrier type, and a proof of
-- its associativity. Agda provides a tool to efficiently define iterated Σ-types using record types:

record SemiGroup {i : Level} : UU (lsuc i) where
    field  
        carrier : UU i
        carrier-is-set : is-set carrier
        mul : carrier → carrier → carrier
        assoc : (x y z : carrier) → Id (mul (mul x y) z) (mul x (mul y z))

open SemiGroup 
-- By opening up SemiGroup, we may access the functions carrier, carrier-is-set, mul, and assoc elsewhere in the file.
-- Thus, record types automatically come with the associated projection functions, rendering the next definition
-- completely unnecessary:

proj-carrier-SemiGroup : {i : Level} → SemiGroup {i} → UU i
proj-carrier-SemiGroup SG = carrier SG

proj-mul-SemiGroup : {i : Level} → (SG : SemiGroup {i}) → carrier SG → carrier SG → carrier SG
proj-mul-SemiGroup SG = mul SG
-- In other words: don't use the functions "proj-carrier-SemiGroup" and "proj-mul-SemiGroup"; 
-- use "carrier" and "mul" instead!

-- Record types also come with a canonical "constructor" which introduces the terms that inductively generate the type.
-- Recall Σ types are inductive types freely generated by ordered pairs of terms.
-- So a record type, being an iterated Σ-type, is freely generated by an ordered list of terms, one for each field.

-- Exercise: redefine the following function by commenting out the definition of is-unital, 
-- typing "is-unital SG = ?" and then loading to open up a hole
-- typing "SG" then C-c C-c in the hole to induct on the variable SG
-- agda should then given the constructor:
-- "{ carrier = carrier ; carrier-is-set = carrier-is-set ; mul = mul ; assoc = assoc }"
-- You can rename the terms after the equals signs to be whatever you want; 
-- eg I've written "\mu" for the multiplication function.
-- Then define what it means for a semi-group to be unital.
-- is-unital : {i : Level} → SemiGroup {i} → UU i
-- is-unital record { carrier = SG ; carrier-is-set = carrier-is-set ; mul = μ ; assoc = assoc } = 
--      Σ SG λ e → ((x : SG) → ((Id (μ e x ) x) × (Id (μ x e) x)))

-- Exercise: prove that any two units in a unital semi-group may be identified
-- unique-unit-is-unital : {i : Level}{G : SemiGroup {i}} → (x y : is-unital G) → Id (pr1 x) (pr1 y)

-- Challenge Exercise: prove that is-unital is a proposition
-- is-prop-is-unital : {i : Level}{SG : SemiGroup {i}} → is-prop (is-unital SG)

-- We can use a record type to define the type of unital semigroups.
record UnitalSemiGroup {i : Level} : UU (lsuc i) where
    field
        SG : SemiGroup {i}
        unit : carrier SG
        left-unit : (x : carrier SG) → Id ((mul SG) unit x) x
        right-unit : (x : carrier SG) → Id ((mul SG) x unit) x

open UnitalSemiGroup 

-- Challenge Exercise: define has-inverses, saying what it means for a unital semi-group to define a group.
-- has-inverses : {i : Level} → UnitalSemiGroup {i} → UU i

-- The syntax for iterated record types can get a bit annoying:
record Group {i : Level} : UU (lsuc i) where
    field
        USG : UnitalSemiGroup {i}
        inverse : carrier (SG (USG)) → carrier (SG (USG))
        left-inverse : (x : carrier (SG (USG))) → Id ((mul (SG (USG))) (inverse x) x) (unit USG)
        right-inverse : (x : carrier (SG (USG))) → Id ((mul (SG (USG))) x (inverse x)) (unit USG)

open Group public

-- The final series of exercises asks you to define a semigroup structure on the type of booleans.

data bool : UU lzero where
    true false : bool

-- Exercise: define an associative binary function on bool. There are multiple choices here, so it's your pick.

-- Exercise: prove that your function is associative

-- The hardest part is to prove that bool is a set. We can cheat by postulating that this is true.
postulate set-bool : is-set bool

-- Exercise: prove that bool is a semigroup. Type semigroup-bool = ? and C-c C-l to load. Then type C-c to C-r
-- to refine and then fill in the holes.
-- semigroup-bool : SemiGroup {lzero}

-- Optional Exercise: if your semigroup of booleans is unital, prove this

-- unital-semigroup-bool : UnitalSemiGroup {lzero}

-- Optional Exercise: if your semigroup is unital and has inverses, construct the associated group

-- group-bool : Group {lzero}

-- Challenge Exercise: get rid of the postulate and instead prove that bool is a set

-- Challenge Exercise: use previous work to show that ℕ is a unital semigroup (perhaps postulating that ℕ is a set)

