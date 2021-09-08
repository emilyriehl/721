{-# OPTIONS --without-K --exact-split --safe #-}
{-
The option --without-K disables Streicher’s K axiom, which we don’t want for univalent mathematics.

The option --exact-split makes Agda to only accept definitions with the equality sign “=” that behave like so-called judgmental or definitional equalities.

The option --safe disables features that may make Agda inconsistent, such as --type-in-type, postulates and more.
-}

module introduction where
-- filename must be module-name.agda

open import Agda.Primitive public
{-
open means we can access all definitions in Agda.Primitive, in this case of a type "Level" of universe levels and terms like lsuc : Level → Level
public means any file that imports this one gets Agda.Primitive too.
-}

--type C-c C-l to load the file. This gives syntax highlighting and tells you if anything is wrong.

UU : (i : Level) → Set (lsuc i)
UU i = Set i
-- type "\to" to get "→"
{-
This code sets up the notation for the universes "UU i" which are types of types.
Formally, "UU" is a function which takes as input a level "i : Level" and produces "UU i", the type of types of level at most i. 
To avoid Russell's paradox, the type "UU i" is a type of the next universe level; in agda's syntax "UU i : Set (lsuc i)".
Here "(i : Level) → Set (lsuc i)" is a dependent function type; by contrast "Level → Set" is a non-dependent function type.
The takeway: to declare that "A is a type of arbitrary universe level" write "A : UU i" in a context where "i : Level".
-}

{- 
I've stollen this from Egbert Rijke's repostory where he's been formalizing the entire HoTT book (https://github.com/HoTT-Intro/Agda).
Solutions to basically all the agda exercises can be found there and to make things simple, I'm trying to make sure our definitions use the same syntax.
-}

-- Section 2.2 The identity function and composition

-- Definition 2.2.3
-- For any type A, we defined the identity function idA : A → A. More precisely, we can think of the type A as an additional parameter in the function id.
-- To be totally general, that type should be allowed to belong to an arbitrary universe level, so really we have a level parameter preceeding the type.
id : {i : Level} {A : UU i} → A → A
id a = a
{-
Here the "{ }" surround implicit arguments which the computer needs to know about but which the user won't supply when calling this function; 
instead the computer will try to infer their values.
After the implicit arguments we see the types of the explicit arguments. 
So id is the name of a function with:
   two implicit arguments (a level and a type of that universe level) and 
   one explicit argument (a term of type A),
   in which the output is a term of type A.
Since the output type "A" is dependent on a term of type "UU i" and this type is in turn dependent on a term of type "Level", 
id is a term of a dependent function type "{i : Level} {A : UU i} → A → A"
-}

-- Exercise 2.3.a: define the constant function const : B → A → B
const : {i j : Level} {A : UU i} {B : UU j} {A : UU i} → B → A → B
const x a = x
-- Type "?" and then load with C-c C-l to open up a "hole".
-- Navigate into the hole and type C-c C-, to check the type needed and the context.
-- Use C-c C-space when you think you've written a term with the correct type.

-- Definition 2.2.5: define _∘_ where you can type "\circ" to get "∘"
-- Similarly composition is a function that involves three types which can belong to arbitrary universes:
_∘_ : {i j k : Level} {A : UU i} {B : UU j} {C : UU k} → (B → C) → (A → B) → (A → C)
(g ∘ f) a = g (f a)


-- We can't solve 2.3.b in agda yet because agda can't prove definitional equalities; you can however ask adga to normalize terms (more about this soon).

-- Exercise 2.4.a
swap : {i j k : Level} {A : UU i} {B : UU j}{ C : A → B → UU k } → ((x : A) → (y : B) → (C x y)) → ((y : B) → (x : A) → (C x y))
swap f = λ y x → f x y
-- use C-c C-r to refine the goal
-- use C-c C-, to check the type needed in each hole
-- use C-c C-space when you think you've written a term with the correct type

-- type "slash b N" to get "ℕ"
data ℕ : UU lzero where
    zero-ℕ : ℕ
    succ-ℕ : ℕ → ℕ
{-
The data type is a magic thing that is used to define inductive types in agda. 
Roughly how it works is you give the formation instruction and the introduction rules. 
The elimination rule (the induction principle) is automatically generated; we'll be able to define the function ind-ℕ below.
But first let's explore general definitions of (dependent) functions on ℕ by pattern matching.
-}

-- You can use previously-defined functions to define new functions.
-- Example: define the function λ n → n + 2 : ℕ → ℕ by giving the formula
add-two-ℕ : ℕ → ℕ
add-two-ℕ = succ-ℕ ∘ succ-ℕ
-- type "add-to-ℕ = ?" and load with C-c C-l
-- type "add-two-ℕ n = ?" then load with C-c C-l. This opens up a "hole"
-- move into the hole and type C-c C-, to see what sort of thing is needed to fill it: in this case, a term of type ℕ → ℕ
-- One way to define add-two-ℕ is as a composite of two successor functions, where the relevant composition function has the type
-- _∘_ : (ℕ → ℕ) → (ℕ → ℕ) → (ℕ → ℕ). You can start by typing "_∘_" then C-c C-r to refine the goal.
-- You're telling agda that you can get a term of type ℕ → ℕ by applying the function _∘_ to something else, in this case two terms of type ℕ → ℕ.
-- Agda then opens up new goals asking for the inputs to the function _∘_.
-- Supply these terms and type C-c C-space to feed them to agda.

-- If you want to check that this is correct, load the file with C-c C-l.
-- Then type C-c C-n to get agda to prompt you to supply a term, such as "add-two-ℕ (succ-ℕ zero-ℕ)" to normalize.

-- Because ℕ was defined as a data type, we can define functions out of ℕ by "pattern matching":
-- Example: definition of predecessor
pred-ℕ : ℕ → ℕ
pred-ℕ zero-ℕ = zero-ℕ
pred-ℕ (succ-ℕ n) = n
-- Type "pred-ℕ n = ?" and load with C-c C-l to open up a hole
-- Move into the hole then type C-c C-c. You'll be asked to supply the variable(s) on which you wish to case split. Type "n".
-- Now agda automatically asks you to define the value of the function pred-ℕ in two cases - zero-ℕ and succ-ℕ n - and supplies two holes to fill in as before.

{-
Summary:
for an inductive type (aka a data type) you can write the name of a variable (or variables) in a hole 
and then C-c C-c to "pattern match" on those variables
agda automatically generates the two cases you need to define a function by recursion on ℕ
adga knows if you gave a valid inductive definition
-}

-- Definition 3.2.1
add-ℕ : ℕ → ℕ → ℕ
add-ℕ m zero-ℕ = m
add-ℕ m (succ-ℕ n) = succ-ℕ (add-ℕ m n)

-- alternatively, we can define addition using double induction
add-ℕ-alt : ℕ → ℕ → ℕ
add-ℕ-alt zero-ℕ zero-ℕ = zero-ℕ
add-ℕ-alt zero-ℕ (succ-ℕ n) = succ-ℕ n
add-ℕ-alt (succ-ℕ m) zero-ℕ = succ-ℕ m
add-ℕ-alt (succ-ℕ m) (succ-ℕ n) = succ-ℕ (succ-ℕ (add-ℕ-alt m n))

-- Recall the rules for ℕ: it is a type in the empty context with two introduction rules:
--   ⊢ zero-ℕ : ℕ   and     ⊢ succ-ℕ : ℕ → ℕ
-- The elimination rule says that given a type family n : ℕ ⊢ P(n) type, a term p0 : P(zero-ℕ), and a dependent function n : ℕ ⊢ pS(n) : P(n) → P(succ-ℕ(n))
-- there is a dependent function n : ℕ ⊢ ind-ℕ(p0,pS,n) : P(n).
-- The computation rules say that ind-ℕ(p0,pS,zero-ℕ) ≐ p0 and ind-ℕ(p0,pS,succ-ℕ(n)) ≐ pS(n,ind-ℕ(p0,pS,n)). Let's now define this function.

-- Remark 3.1.2: define ind-ℕ, the function that expresses the ℕ-elimination rule
ind-ℕ : {i : Level} {P : ℕ → UU i} → P zero-ℕ → ((n : ℕ) → P n → P(succ-ℕ n)) → ((n : ℕ) → P n)
ind-ℕ p0 pS zero-ℕ = p0
ind-ℕ p0 pS (succ-ℕ n) = pS n (ind-ℕ p0 pS n)
-- start with ind­-ℕ p0 pS n = ? then C-c C-l then C-c C-c to case split on n

-- for instance, we can use this to define a function by recursion.
rec-ℕ : {i : Level} {X : UU i} → X → (X → X) → (ℕ → X)
rec-ℕ x0 f = ind-ℕ x0 (λ n x → f x) 

-- turn off safe flag then
{-
postulate
    i : Level
    X : UU i
    x0 : X
    f : X → X
-- C-c C-n to open up something to normalize
-- type rec-ℕ x0 f (succ-ℕ (succ-ℕ zero-ℕ))
-}

gen-rec-ℕ : {i : Level} {X : UU i} → X → (ℕ → X → X) → (ℕ → X)
gen-rec-ℕ x0 g = ind-ℕ x0 g

