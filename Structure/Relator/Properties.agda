module Structure.Relator.Properties lvl where

open import Data
open import Functional
open import Logic(lvl)
open import Numeral.Natural
open import NonEmptyList as List
  using (List ; _⤙_ ; _⤛_ ; End)

infixl 1000 _🝖_

FlipPattern : {T₁ T₂ : Set} → (T₁ → T₂ → Stmt) → (T₂ → T₁ → Stmt) → Stmt
FlipPattern {T₁} {T₂} (_▫₁_) (_▫₂_) = {x : T₁}{y : T₂} → (x ▫₁ y) → (y ▫₂ x)

Reflexivity : {T : Set} → (T → T → Stmt) → Stmt
Reflexivity {T} (_▫_) = {x : T} → (x ▫ x)

Transitivity : {T : Set} → (T → T → Stmt) → Stmt
Transitivity {T} (_▫_) = {x y z : T} → ((x ▫ y) ∧ (y ▫ z)) → (x ▫ z)

Antisymmetry : {T : Set} → (T → T → Stmt) → (T → T → Stmt) → Stmt
Antisymmetry {T} (_▫₁_) (_▫₂_) = {a b : T} → ((a ▫₁ b) ∧ (b ▫₁ a)) → (a ▫₂ b)

Irreflexivity : {T : Set} → (T → T → Stmt) → Stmt
Irreflexivity {T} (_▫_) = {x : T} → ¬(x ▫ x)

Total : {T : Set} → (T → T → Stmt) → Stmt
Total {T} (_▫_) = {x y : T} → (x ▫ y) ∨ (y ▫ x)

-- Dichotomy : {T : Stmt} → (T → T → Stmt) → Stmt
-- Dichotomy {T} (_▫_) = {x y : T} → (x ▫ y) ⊕ (y ▫ x)

-- Trichotomy : {T : Stmt} → (T → T → Stmt) → Stmt
-- Trichotomy {T} (_▫₁_) (_▫₂_) = {x y : T} → (x ▫₁ y) ⊕ (y ▫₁ x) ⊕ (x ▫₂ y) -- TODO: Not correct. Should only be one of them

-- For constructions/proofs of this form: Proof of a=f: a=b ∧ b=c ∧ c=d ∧ d=e ∧ e=f (also expressed as a=b=c=d=e=f)
TransitivityChain : ∀{n}{T : Set n} → (T → T → Stmt) → (List 1 T) → Stmt
TransitivityChain {T} (_▫_) X = (List.reduceₗ (_∧_) (List.fromList (List.mapWindow2ₗ (_▫_) X) ⊥)) → ((List.firstElem X) ▫ (List.lastElem X))

---------------------------------------------------------
-- Derived

Converse : {T₁ T₂ : Set} → (T₁ → T₂ → Stmt) → (T₂ → T₁ → Stmt) → Stmt
Converse {T₁} {T₂} (_▫₁_) (_▫₂_) =
  FlipPattern (_▫₁_) (_▫₂_) ∧ FlipPattern (_▫₂_) (_▫₁_)
-- {x : T₁}{y : T₂} → (x ▫₁ y) ↔ (y ▫₂ x)

Symmetry : {T : Set} → (T → T → Stmt) → Stmt
Symmetry {T} (_▫_) = FlipPattern (_▫_) (_▫_)
-- {x y : T} → (x ▫ y) → (y ▫ x)

Asymmetry : {T : Set} → (T → T → Stmt) → Stmt
Asymmetry {T} (_▫_) = FlipPattern (_▫_) (λ x y → ¬(x ▫ y))
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

-- testTransitivityChain : {_▫_ : ℕ → ℕ → Stmt} → TransitivityChain _▫_ (1 ⤙ 2 ⤙ 3 ⤛ 4) → ((1 ▫ 2) ∧ (2 ▫ 3) ∧ (3 ▫ 4)) → (1 ▫ 4)
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
_🝖_ : ∀{T _▫_} {{_ : Transitivity {T} (_▫_)}} → ∀{x y z} → (x ▫ y) → (y ▫ z) → (x ▫ z)
_🝖_ {_} {_} {{trans}} a b = trans([∧]-intro a b)
