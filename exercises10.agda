{-# OPTIONS --without-K --exact-split #-}
-- Note we've removed the "safe" tag so that we can postulate everything

module exercises10 where
{-
Please rename your file to exercises10-yourusername.agda
-}

open import Agda.Primitive public

UU : (i : Level) โ Set (lsuc i)
UU i = Set i

-- The one-sided identity type is the type family
data Id {i : Level}{A : UU i}(a : A) : A โ UU i where
    refl : Id a a

-- Exercise: uncomment the following code and note that agda doesn't like it
-- data ๐ยน : UU lzero where
--     base : ๐ยน
--     loop : Id base base
-- In other words, agda doesn't natively support higher inductive types, so we'll instead have to postulate 
-- everything we'd like to know about ๐ยน.

-- type "\bS\^1" for "๐ยน"
postulate ๐ยน : UU lzero

postulate base-๐ยน : ๐ยน

postulate loop-๐ยน : Id base-๐ยน base-๐ยน

-- Since we haven't defined ๐ยน to be any sort of inductive type we don't have the elimination and computation rules
-- associated to ๐ยน. We must first define the types that state these and then postulate proofs.
-- For simplicity, we'll only discuss the non-dependent universal property of the circle.

-- The dependent pair type
data ฮฃ {i j : Level}(A : UU i)(B : A โ UU j) : UU(i โ j) where
    pair : (x : A) โ B x โ ฮฃ A B

_ร_ : {i j : Level}(A : UU i)(B : UU j) โ UU (i โ j)
A ร B = ฮฃ A (ฮป x โ B)

pr1 : {i j : Level}{A : UU i}{B : A โ UU j} โ ฮฃ A B โ A
pr1 (pair a b) = a 

pr2 : {i j : Level}{A : UU i}{B : A โ UU j} โ (z : ฮฃ A B) โ B (pr1 z)
pr2 (pair a b) = b 

-- Exercise: for a type X define a type "free-loops X" that consists of pairs given by an x : X and a loop p : x = x
-- Its terms are "free loops" in X, meaning loops on any base point.
-- free-loops : {i : Level} โ (X : UU i) โ UU i

-- Exercise: define a function constant-loops that takes a point in X to the constant loop at that point
-- constant-loops : {i : Level} {X : UU i} โ X โ free-loops X

-- Exercise: define base-free-loops : (free-loops X) โ X projecting from a free loop to its base point
-- base-free-loops : {i : Level} {X : UU i} โ free-loops X โ X

-- Exercise: define loop-free-loops, a dependent function that sends a free loop to the loop at its base point
-- loop-free-loops : {i : Level} {X : UU i} โ (p : free-loops X) โ Id (base-free-loops p) (base-free-loops p)

-- Concatenation and inversion of paths
_ยท_ : {i : Level}{A : UU i}{x y z : A} โ (Id x y) โ (Id y z) โ (Id x z)
refl ยท q = q

inv : {i : Level}{A : UU i}{x y : A} โ Id x y โ Id y x
inv refl = refl

data โ : UU lzero where
    zero-โ : โ
    succ-โ : โ โ โ

-- Challenge Exercise: for each n : โ, define "n fold-loop", a function that sends a loop p at x to the loop given by 
-- the n-fold concatenation of p with itself. 
-- First, try to define this function directly. If agda complains that some identification does not hold judgmentally
-- the auxiliary function "n th loop" might help.
-- _th-loop_ : {i : Level}{X : UU i} โ โ โ (p : free-loops X) โ Id (base-free-loops p) (base-free-loops p)

-- _fold-loop_ : {i : Level}{X : UU i} โ โ โ free-loops X โ free-loops X
-- n fold-loop p = ?

-- Exercise: use the postulates to define a canonical term free-loop-๐ยน : free-loops ๐ยน
-- free-loop-๐ยน : free-loops ๐ยน

-- Definition 5.3.1: the application of functions on paths
ap : {i j : Level}{A : UU i}{B : UU j}{x y : A} โ (f : A โ B) โ (Id x y) โ (Id (f x) (f y))
ap f refl = refl

-- Exercise: define ev-free-loop : (๐ยน โ X) โ free-loops X that evaluates a function on the canonical free loop
-- ev-free-loop : {i : Level}{X : UU i} โ (๐ยน โ X) โ free-loops X

-- Definition 9.1.2: the type of homotopies "f โผ g" for a pair of dependent functions; type "\sim" for "โผ"
_โผ_ : {i j : Level}{A : UU i}{B : A โ UU j} โ (f g : (a : A) โ B a) โ UU(i โ j)
f โผ g = (x : _) โ Id (f x) (g x)

-- function composition and identity
_โ_ : {i j k : Level}{A : UU i}{B : UU j}{C : UU k} โ (B โ C) โ (A โ B) โ (A โ C)
g โ f = ฮป x โ g (f x)

id : {i : Level}(A : UU i) โ A โ A
id A a = a

-- equivalences and contractible types
sec : {i j : Level}{A : UU i}{B : UU j} โ (A โ B) โ UU(i โ j)
sec {A = A}{B = B} f = ฮฃ (B โ A) ฮป s โ (f โ s) โผ id B

retr : {i j : Level}{A : UU i}{B : UU j} โ (A โ B) โ UU(i โ j)
retr {A = A}{B = B} f = ฮฃ (B โ A) ฮป r โ (r โ f) โผ id A

is-equiv : {i j : Level}{A : UU i}{B : UU j} โ (A โ B) โ UU(i โ j)
is-equiv f = (sec f) ร (retr f)

-- The non-dependent induction principle for ๐ยน postulates the existence of a section for ev-free-loop
-- Uncomment this after you've defined the function ev-free-loop
-- postulate ๐ยน-induction : {i : Level}{X : UU i} โ sec (ev-free-loop {X = X})

-- Exercise: from the postulate ๐ยน-induction define ind-๐ยน, the section to ev-free-loop
-- ind-๐ยน : {i : Level}{X : UU i} โ free-loops X โ (๐ยน โ X)

-- Exercise: from the postulate ๐ยน-induction define comp-๐ยน, the homotopy
-- comp-๐ยน : {i : Level}{X : UU i} โ (ev-free-loop โ ind-๐ยน) โผ id (free-loops X)

-- For a pair (x : X, p : x = x) in free-loops X, "comp-๐ยน (pair x p): is an identification in the ฮฃ-type free-loops X
-- It will be more useful to extract a pair of paths from this single path, for which we use the function defined 
-- on exercises9.

-- Definition 5.4.1: the transport function
tr : {i j : Level}{A : UU i}(B : A โ UU j){x y : A} โ (Id x y) โ (B x) โ (B y)
tr B refl b = b

-- The identity type of ฮฃ types are equivalent to a type "pair-of-paths" given by 
-- a path p : a = a' in A and a path q : (tr B p b) = b' in B(a').
pair-of-paths : {i j : Level}{A : UU i}{B : A โ UU j} โ (x y : ฮฃ A B) โ UU (i โ j)
pair-of-paths (pair a b) (pair a' b') = ฮฃ (Id a a') ฮป p โ Id (tr _ p b) b'

-- The function that converts a path in the identity type of ฮฃ A B into a pair of paths
pair-of-paths-path-ฮฃ : {i j : Level}{A : UU i}{B : A โ UU j} โ (x y : ฮฃ A B) โ Id x y โ pair-of-paths x y
pair-of-paths-path-ฮฃ (pair x xโ) .(pair x xโ) refl = pair refl refl

-- Challenge Exercise: define base-comp-๐ยน, the base path from comp-๐ยน associated to (pair x p) : free-loops X
-- base-comp-๐ยน : {i : Level}{X : UU i} โ (l : free-loops X) โ Id ((ind-๐ยน l) base-๐ยน) (base-free-loops l)

-- Challenge Exercise: define loop-comp-๐ยน, the path of loops from comp-๐ยน associated to (pair x p) : free-loops X
-- loop-comp-๐ยน : {i : Level}{X : UU i} โ (l : free-loops X) 
--         โ Id (tr (ฮป z โ Id z z) (base-comp-๐ยน l) (ap (ind-๐ยน l) loop-๐ยน)) (loop-free-loops l)

-- If we had developed the dependent induction principle for ๐ยน the terms ind-๐ยน and comp-๐ยน would be enough
-- to prove that ev-free-loop is an equivalence. Since we're doing the non-dependent version, we really should 
-- have postulated that ev-free-loop is an equivalence.

-- We conclude with some applications of ind-๐ยน.

-- Exercise: define a "degree-two" function from ๐ยน to ๐ยน that sends base-๐ยน to base-๐ยน and 
-- loop-๐ยน to loop-๐ยน ยท loop-๐ยน.
-- deg-two : ๐ยน โ ๐ยน

-- Challenge Exercise: for any n : โ, define a "degree n" function from ๐ยน to ๐ยน that sends base-๐ยน to base-๐ยน and -- loop-๐ยน to the n-fold concatentation of loop-๐ยน with itself
-- deg : โ โ ๐ยน โ ๐ยน

-- Challenge Exercise: extend the previously-defined degree function from โ to โค by sending a negative integer -n
-- to the function that sends loop-๐ยน to the n-fold concantenation of the reverse of loop-๐ยน with itself
-- Since we don't have the unit type or coproduct types, we just define the integers directly:

data โค : UU lzero where
    zero-โค : โค
    pos-โค : โ โ โค -- inclusion of the positive integers
    neg-โค : โ โ โค -- inclusion of the negative integers

-- degree : โค โ ๐ยน โ ๐ยน

