module Structure.Relator.Properties {ℓ₁}{ℓ₂} where

import      Lvl
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Functional
open import Logic.Propositional{ℓ₁ Lvl.⊔ ℓ₂}
open import Numeral.Natural
open import Type{ℓ₂}

ConversePattern : {T₁ T₂ : Type} → (T₁ → T₂ → Stmt) → (T₂ → T₁ → Stmt) → Stmt
ConversePattern {T₁} {T₂} (_▫₁_) (_▫₂_) = (∀{x : T₁}{y : T₂} → (x ▫₁ y) → (y ▫₂ x))

-- TODO: Maybe use `abstract` blocks instead of `records`? The reason for having records is after all to get ⦃⦄-implicits working.

-- Definition of a reflexive binary relation
record Reflexivity {T : Type} (_▫_ : T → T → Stmt) : Stmt where
  constructor intro

  field
    reflexivity : ∀{x : T} → (x ▫ x)
open Reflexivity ⦃ ... ⦄ public

-- Definition of a transitive binary relation
record Transitivity {T : Type} (_▫_ : T → T → Stmt) : Stmt where
  constructor intro

  field
    transitivity : ∀{x y z : T} → (x ▫ y) → (y ▫ z) → (x ▫ z)

  -- The transitivity operator
  infixl 1000 _🝖_
  _🝖_ : ∀{x y z} → (x ▫ y) → (y ▫ z) → (x ▫ z)
  _🝖_ {T} (A)(B) = transitivity{T} (A)(B)

open Transitivity ⦃ ... ⦄ public

-- Definition of a antisymmetric binary relation
record Antisymmetry {T : Type} (_▫₁_ _▫₂_ : T → T → Stmt) : Stmt where
  constructor intro

  field
    antisymmetry : ∀{a b : T} → (a ▫₁ b) → (b ▫₁ a) → (a ▫₂ b)
open Antisymmetry ⦃ ... ⦄ public

-- Definition of a irreflexive binary relation
record Irreflexivity {T : Type} (_▫_ : T → T → Stmt) : Stmt where
  constructor intro

  field
    irreflexivity : ∀{x : T} → ¬(x ▫ x)
open Irreflexivity ⦃ ... ⦄ public

-- Definition of a total binary relation.
-- Total in the sense that it, or its converse, holds.
record ConverseTotal {T : Type} (_▫_ : T → T → Stmt) : Stmt where
  constructor intro

  field
    converseTotal : ∀{x y : T} → (x ▫ y) ∨ (y ▫ x)
open ConverseTotal ⦃ ... ⦄ public

-- Dichotomy : {T : Type}} → (T → T → Stmt) → Stmt
-- Dichotomy {T} (_▫_) = {x y : T} → (x ▫ y) ⊕ (y ▫ x)

-- Trichotomy : {T : Type} → (T → T → Stmt) → Stmt
-- Trichotomy {T} (_▫₁_) (_▫₂_) = {x y : T} → (x ▫₁ y) ⊕ (y ▫₁ x) ⊕ (x ▫₂ y) -- TODO: Not correct. Should only be one of them

-- For constructions/proofs of this form: Proof of a=f: a=b ∧ b=c ∧ c=d ∧ d=e ∧ e=f (also expressed as a=b=c=d=e=f)
-- TransitivityChain : {T : Type} → (T → T → Stmt) → (List 1 T) → Stmt
-- TransitivityChain {T} (_▫_) X = (List.reduceₗ (_∧_) (List.fromList (List.mapWindow2ₗ (_▫_) X) ⊥)) → ((List.firstElem X) ▫ (List.lastElem X))

---------------------------------------------------------
-- Derived

-- Definition of a converse binary operation for a binary operation
record Converse {T₁ T₂ : Type} (_▫₁_ : T₁ → T₂ → Stmt) (_▫₂_ : T₂ → T₁ → Stmt) : Stmt where
  constructor intro

  field
    converseₗ : ConversePattern (_▫₂_) (_▫₁_)
    converseᵣ : ConversePattern (_▫₁_) (_▫₂_)
open Converse ⦃ ... ⦄ public
-- {x : T₁}{y : T₂} → (x ▫₁ y) ↔ (y ▫₂ x)

-- Definition of a symmetric binary operation
record Symmetry {T : Type} (_▫_ : T → T → Stmt) : Stmt where
  constructor intro

  field
    symmetry : ConversePattern (_▫_) (_▫_)
open Symmetry ⦃ ... ⦄ public
-- {x y : T} → (x ▫ y) → (y ▫ x)

-- Definition of an asymmetric binary operation
record Asymmetry {T : Type} (_▫_ : T → T → Stmt) : Stmt where
  constructor intro

  field
    asymmetry : ConversePattern (_▫_) (x ↦ y ↦ ¬(x ▫ y))
open Asymmetry ⦃ ... ⦄ public
-- {x y : T} → (x ▫ y) → ¬(y ▫ x)

---------------------------------------------------------
-- Functions

-- TODO
-- transitivityChain : ∀{T _▫_}{X : List 1 T} → Transitivity (_▫_) → TransitivityChain (_▫_) X
-- transitivityChain {_} {_} {list} trans _ = (a(List.length list)) (b(List.length list)) where
--   a : ℕ → (_)
--   a 0     = id
--   a 1     = id
--   a 2     = id
--   a(𝐒(n)) = Tuple.uncurry ∘ (a(n))
--
--   b : ℕ → (_)
--   b 0     = id
--   b 1     = id
--   b 2     = id
--   b(𝐒(n)) = Tuple.curry((b(n)) ∘ trans)
-- Old idea: trans(transitivityChain trans tail)

-- testTransitivityChain : {_▫_ : ℕ → ℕ → Stmt} → TransitivityChain _▫_ (1 ⊰ 2 ⊰ 3 ⤛ 4) → ((1 ▫ 2) ∧ (2 ▫ 3) ∧ (3 ▫ 4)) → (1 ▫ 4)
-- testTransitivityChain x = x

-- testTransitivityChain : {_▫_ : ℕ → ℕ → Stmt} → Transitivity (_▫_) → ((1 ▫ 2) ∧ (2 ▫ 3) ∧ (3 ▫ 4)) → (1 ▫ 4)
-- testTransitivityChain trans (x , y , z) = trans((trans(x , y)) , z)

-- testTransitivityChain : {_▫_ : ℕ → ℕ → Stmt} → Transitivity (_▫_) → ((1 ▫ 2) ∧ (2 ▫ 3) ∧ (3 ▫ 4)) → (1 ▫ 4)
-- testTransitivityChain trans (x , y , z) = (Tuple.curry trans)((Tuple.curry trans) x y)  z

-- testTransitivityChain : {_▫_ : ℕ → ℕ → Stmt} → Transitivity (_▫_) → ((1 ▫ 2) ∧ (2 ▫ 3) ∧ (3 ▫ 4)) → (1 ▫ 4)
-- testTransitivityChain trans (xy , z) = (Tuple.curry trans)(trans xy)  z

-- testTransitivityChain : {_▫_ : ℕ → ℕ → Stmt} → Transitivity (_▫_) → ((1 ▫ 2) ∧ (2 ▫ 3) ∧ (3 ▫ 4)) → (1 ▫ 4)
-- testTransitivityChain trans =
--   (Tuple.uncurry ∘ Tuple.uncurry) (Tuple.curry((Tuple.curry trans) ∘ trans))
-- f :: ((Integer,Integer),(Integer,Integer)) -> (Integer,Integer)
-- f((x,_),(_,y)) = (x,y)
-- (uncurry.uncurry) (curry((curry f).f)) (((1,10),(20,2)),(30,3)) = (1,3)

-- testTransitivityChain : {_▫_ : ℕ → ℕ → Stmt} → Transitivity (_▫_) → ((1 ▫ 2) ∧ (2 ▫ 3) ∧ (3 ▫ 4) ∧ (4 ▫ 5)) → (1 ▫ 5)
-- testTransitivityChain trans =
--   (Tuple.uncurry ∘ Tuple.uncurry ∘ Tuple.uncurry) (Tuple.curry(Tuple.curry((Tuple.curry trans) ∘ trans) ∘ trans))

-- Transitivity as a binary operation (TODO: The symbol is supposed to be the alchemical symbol for horse dung, but it was the best I could find that somewhat represented transitivity)
-- _🝖_ : ∀{T _▫_} ⦃ _ : Transitivity {T} (_▫_) ⦄ → ∀{x y z} → (x ▫ y) → (y ▫ z) → (x ▫ z)
-- _🝖_ {_} {_} ⦃ trans ⦄ a b = trans([∧]-intro a b)

-- TODO: Maybe try to make transitivity proofs more like regular math syntax-wise:
-- _ _[Trans:_with_] : (x ▫ y) → ((y ▫ z) : T) → T → (Transitivity _▫_) → (x ▫ z) -- TODO: T and (y ▫ z) is reversed?
-- (x ≡ 2 ⋅ (a + 1))
-- (_ ≡ (a + 1)+(a + 1))   [Trans: [⋅]-to-[+]                        with [≡]-transitivity]
-- (_ ≡ a + (1 + (a + 1))) [Trans: [+]-associativity                 with [≡]-transitivity]
-- (_ ≡ a + ((a + 1) + 1)) [Trans: ([≡]-with[_] ∘ [+]-commutativity) with [≡]-transitivity]
-- (_ ≡ a + (a + (1 + 1))) [Trans: ([≡]-with[_] ∘ [+]-associativity) with [≡]-transitivity]
-- (_ ≡ (a + a) + (1 + 1)) [Trans: [+]-associativity                 with [≡]-transitivity]
