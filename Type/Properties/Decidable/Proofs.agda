module Type.Properties.Decidable.Proofs where

open import Data
open import Data.Proofs
open import Data.Boolean using (if_then_else_)
open import Data.Boolean.Stmt
open import Data.Either as Either using (_‖_)
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Functional
import      Lvl
open import Data.Boolean using (Bool ; 𝑇 ; 𝐹)
import      Data.Boolean.Operators
open        Data.Boolean.Operators.Programming
open import Lang.Inspect
open import Logic
open import Logic.Classical
open import Logic.Predicate
open import Logic.Propositional
open import Numeral.Natural
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Type.Properties.Decidable
open import Type.Properties.Empty
open import Type.Properties.Inhabited
open import Type.Properties.Singleton.Proofs
open import Type

private variable ℓ ℓₚ : Lvl.Level
private variable A B C P Q R T : Type{ℓ}
private variable b b₁ b₂ d : Bool
private variable f g : A → B

module _ (P : Stmt{ℓ}) where
  decider-classical : ⦃ dec : Decider₀(P)(d) ⦄ → Classical(P)
  Classical.excluded-middle (decider-classical ⦃ dec = dec ⦄) = elim(\_ → (P ∨ (¬ P))) [∨]-introₗ [∨]-introᵣ dec

  classical-decidable : ⦃ classical : Classical(P) ⦄ → Decidable(0)(P)
  ∃.witness classical-decidable = Either.isLeft(excluded-middle(P))
  ∃.proof   classical-decidable with excluded-middle(P) | inspect Either.isLeft(excluded-middle(P))
  ... | Either.Left  p  | _ = true  p
  ... | Either.Right np | _ = false np

  module _ {ℓ₂} {x y : R} {Pred : (P ∨ (¬ P)) → R → Type{ℓ₂}} where
    decider-if-intro : ∀{f} ⦃ dec : Decider₀(P)(f) ⦄ → ((p : P) → Pred(Either.Left p)(x)) → ((np : (¬ P)) → Pred(Either.Right np)(y)) → Pred(excluded-middle(P) ⦃ decider-classical ⦄)(if f then x else y)
    decider-if-intro {f = 𝑇} ⦃ true  p  ⦄ fp _   = fp  p
    decider-if-intro {f = 𝐹} ⦃ false np ⦄ _  fnp = fnp np

decider-to-classical : ⦃ dec : Decider₀(P)(d) ⦄ → Classical(P)
decider-to-classical{P = P} = decider-classical(P)

classical-to-decidable : ⦃ classical : Classical(P) ⦄ → Decidable(0)(P)
classical-to-decidable{P = P} = classical-decidable(P)

classical-to-decider : ⦃ classical : Classical(P) ⦄ → Decider(0)(P)([∃]-witness classical-to-decidable)
classical-to-decider{P = P} = [∃]-proof classical-to-decidable

decider-true : ⦃ dec : Decider₀(P)(b) ⦄ → (P ↔ IsTrue(b))
decider-true ⦃ dec = true  p ⦄  = [↔]-intro (const p) (const <>)
decider-true ⦃ dec = false np ⦄ = [↔]-intro empty (empty ∘ np)

decider-false : ⦃ dec : Decider₀(P)(b) ⦄ → ((P → Empty{ℓ}) ↔ IsFalse(b))
decider-false ⦃ dec = true  p ⦄  = [↔]-intro empty (empty ∘ apply p)
decider-false ⦃ dec = false np ⦄ = [↔]-intro (const(empty ∘ np)) (const <>)

isempty-decider : ⦃ empty : IsEmpty(P) ⦄ → Decider₀(P)(𝐹)
isempty-decider ⦃ intro p ⦄ = false (empty ∘ p)

inhabited-decider : ⦃ inhab : (◊ P) ⦄ → Decider₀(P)(𝑇)
inhabited-decider ⦃ intro ⦃ p ⦄ ⦄ = true p

empty-decider : Decider₀(Empty{ℓ})(𝐹)
empty-decider = isempty-decider

unit-decider : Decider₀(Unit{ℓ})(𝑇)
unit-decider = inhabited-decider ⦃ unit-is-pos ⦄

instance
  tuple-decider : ⦃ dec-P : Decider₀(P)(b₁) ⦄ → ⦃ dec-Q : Decider₀(Q)(b₂) ⦄ → Decider₀(P ⨯ Q)(b₁ && b₂)
  tuple-decider ⦃ true  p ⦄  ⦃ true  q ⦄  = true(p , q)
  tuple-decider ⦃ true  p ⦄  ⦃ false nq ⦄ = false(nq ∘ Tuple.right)
  tuple-decider ⦃ false np ⦄ ⦃ true  q ⦄  = false(np ∘ Tuple.left)
  tuple-decider ⦃ false np ⦄ ⦃ false nq ⦄ = false(np ∘ Tuple.left)

instance
  either-decider : ⦃ dec-P : Decider₀(P)(b₁) ⦄ → ⦃ dec-Q : Decider₀(Q)(b₂) ⦄ → Decider₀(P ‖ Q)(b₁ || b₂)
  either-decider ⦃ true  p ⦄  ⦃ true  q ⦄  = true (Either.Left p)
  either-decider ⦃ true  p ⦄  ⦃ false nq ⦄ = true (Either.Left p)
  either-decider ⦃ false np ⦄ ⦃ true  q ⦄  = true (Either.Right q)
  either-decider ⦃ false np ⦄ ⦃ false nq ⦄ = false (Either.elim np nq)

instance
  function-decider : ⦃ dec-P : Decider₀(P)(b₁) ⦄ → ⦃ dec-Q : Decider₀(Q)(b₂) ⦄ → Decider₀(P → Q)((! b₁) || b₂)
  function-decider ⦃ true  p ⦄  ⦃ true  q ⦄  = true (const q)
  function-decider ⦃ true  p ⦄  ⦃ false nq ⦄ = false (apply p ∘ (nq ∘_))
  function-decider ⦃ false np ⦄ ⦃ true  q ⦄  = true (const q)
  function-decider ⦃ false np ⦄ ⦃ false nq ⦄ = true (empty ∘ np)

instance
  not-decider : ⦃ dec : Decider₀(P)(b) ⦄ → Decider₀(¬ P)(! b)
  not-decider = function-decider {b₂ = 𝐹} ⦃ dec-Q = empty-decider ⦄

instance
  IsTrue-decider : Decider₀(IsTrue(b))(b)
  IsTrue-decider {𝑇} = true <>
  IsTrue-decider {𝐹} = false id

decider-relator : (P ↔ Q) → (b₁ ≡ b₂) → Decider₀(P)(b₁) ↔ Decider₀(Q)(b₂)
decider-relator pq [≡]-intro  = [↔]-intro
  (\{(true q) → true([↔]-to-[←] pq q) ; (false nq) → false(nq ∘ [↔]-to-[→] pq)})
  (\{(true p) → true([↔]-to-[→] pq p) ; (false np) → false(np ∘ [↔]-to-[←] pq)})
