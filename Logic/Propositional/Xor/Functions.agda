module Logic.Propositional.Xor.Functions where

open import BidirectionalFunction using (_$ₗ_ ; _$ᵣ_)
open import Data.Boolean using (Bool ; 𝑇 ; 𝐹)
import      Data.Tuple as Tuple
open import Functional as Fn using (id ; const ; _∘_ ; _∘₂_)
import      Lvl
open import Logic.Propositional
open import Type

private variable ℓ : Lvl.Level
private variable A B C A₁ A₂ B₁ B₂ : Type{ℓ}

elim : (P : A ⊕ B → Type{ℓ}) → ((a : A) → (nb : ¬ B) → P([⊕]-introₗ a nb)) → ((na : ¬ A) → (b : B) → P([⊕]-introᵣ b na)) → ((e : A ⊕ B) → P(e))
elim _ l r ([⊕]-introₗ a nb) = l a nb
elim _ l r ([⊕]-introᵣ b na) = r na b

map1 : let _ = A ; _ = B ; _ = C in (A → (¬ B) → C) → ((¬ A) → B → C) → (A ⊕ B) → C
map1 = elim _

isLeft : A ⊕ B → Bool
isLeft = map1 (const(const 𝑇)) (const(const 𝐹))

isRight : A ⊕ B → Bool
isRight = map1 (const(const 𝐹)) (const(const 𝑇))

swap : A ⊕ B → B ⊕ A
swap = map1 [⊕]-introᵣ (Fn.swap [⊕]-introₗ)

mapBidirectional : (A₁ ↔ A₂) → (B₁ ↔ B₂) → (A₁ ⊕ B₁) → (A₂ ⊕ B₂)
mapBidirectional fa fb = map1(\a nb → [⊕]-introₗ (fa $ᵣ a) (nb ∘ (fb $ₗ_))) (\na b → [⊕]-introᵣ (fb $ᵣ b) (na ∘ (fa $ₗ_)))

map2 : ((A₁ ∧ ¬ B₁) → (A₂ ∧ ¬ B₂)) → ((¬ A₁ ∧ B₁) → (¬ A₂ ∧ B₂)) → (A₁ ⊕ B₁) → (A₂ ⊕ B₂)
map2 fa fb = map1 (Tuple.curry(Tuple.uncurry [⊕]-introₗ ∘ fa)) (Tuple.curry(Tuple.uncurry (Fn.swap [⊕]-introᵣ) ∘ fb))
