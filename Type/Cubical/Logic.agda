{-# OPTIONS --cubical #-}

module Type.Cubical.Logic where

open import Functional
import      Logic.Propositional as Logic
import      Logic.Predicate     as Logic
import      Lvl
open import Type
open import Type.Cubical.Path.Equality
open import Type.Cubical.HTrunc₁
open import Type.Properties.MereProposition

private variable ℓ ℓ₁ ℓ₂ : Lvl.Level
private variable T A B C Obj : Type{ℓ}
private variable Pred : Obj → Type{ℓ}

open import Logic.Propositional public using
  ( _∧_ ; [∧]-intro ; [∧]-elimₗ ; [∧]-elimᵣ
  ; _←_ ; [←]-intro ; [←]-elim
  ; _↔_ ; [↔]-intro ; [↔]-elimₗ ; [↔]-elimᵣ ; [↔]-to-[←] ; [↔]-to-[→]
  ; ¬_  ; [¬]-intro ; [¬]-elim
  ; ⊥   ; [⊥]-elim
  ; ⊤   ; [⊤]-intro
  )

-- Generally, Logic._∨_ have at most two inhabitants.
-- It is therefore not a mere proposition and here it is truncated to being one.
_∨_ : Type{ℓ₁} → Type{ℓ₂} → Type
_∨_ = HTrunc₁ ∘₂ (Logic._∨_)

[∨]-introₗ : A → (A ∨ B)
[∨]-introₗ = trunc ∘ Logic.[∨]-introₗ

[∨]-introᵣ : B → (A ∨ B)
[∨]-introᵣ = trunc ∘ Logic.[∨]-introᵣ

[∨]-elim : ⦃ prop-C : MereProposition(C) ⦄ → (A → C) → (B → C) → (A ∨ B) → C
[∨]-elim = HTrunc₁-function ∘₂ Logic.[∨]-elim

instance
  [∨]-prop : MereProposition(A ∨ B)
  [∨]-prop = HTrunc₁-prop

-- Generally, Logic.∃ have at most the same amount of inhabitants as its Obj if the predicate is a mere proposition for every argument.
-- It is therefore not a mere proposition and here it is truncated to being one.
∃ : (Obj → Type{ℓ}) → Type
∃ = HTrunc₁ ∘ Logic.∃

[∃]-intro : (witness : Obj) → ⦃ proof : Pred(witness) ⦄ → ∃(Pred)
[∃]-intro witness = trunc(Logic.[∃]-intro witness)

[∃]-elim : ⦃ prop-A : MereProposition(A) ⦄ → (∀{x : Obj} → Pred(x) → A) → ∃(Pred) → A
[∃]-elim = HTrunc₁-function ∘ Logic.[∃]-elim

instance
  [∃]-prop : MereProposition(∃ Pred)
  [∃]-prop = HTrunc₁-prop
