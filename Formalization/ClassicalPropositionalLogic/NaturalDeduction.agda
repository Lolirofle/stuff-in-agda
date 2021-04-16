module Formalization.ClassicalPropositionalLogic.NaturalDeduction where

open import Data.Either as Either using (Left ; Right)
open import Formalization.ClassicalPropositionalLogic.Syntax
open import Functional
import      Lvl
import      Logic.Propositional as Meta
open import Logic
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Sets.PredicateSet using (PredSet ; _∈_ ; _∉_ ; _∪_ ; _∪•_ ; _∖_ ; _⊆_ ; _⊇_ ; ∅ ; [≡]-to-[⊆] ; [≡]-to-[⊇]) renaming (•_ to singleton ; _≡_ to _≡ₛ_)
open import Type

private variable ℓₚ ℓ ℓ₁ ℓ₂ : Lvl.Level

data _⊢_ {ℓ ℓₚ} {P : Type{ℓₚ}} : Formulas(P){ℓ} → Formula(P) → Stmt{Lvl.𝐒(ℓₚ Lvl.⊔ ℓ)} where
  direct : ∀{Γ} → (Γ ⊆ (Γ ⊢_))

  [⊤]-intro : ∀{Γ} → (Γ ⊢ ⊤)

  [⊥]-intro : ∀{Γ}{φ} → (Γ ⊢ φ) → (Γ ⊢ (¬ φ)) → (Γ ⊢ ⊥)
  [⊥]-elim  : ∀{Γ}{φ} → (Γ ⊢ ⊥) → (Γ ⊢ φ)

  [¬]-intro : ∀{Γ}{φ} → ((Γ ∪ singleton(φ)) ⊢ ⊥) → (Γ ⊢ (¬ φ))
  [¬]-elim  : ∀{Γ}{φ} → ((Γ ∪ singleton(¬ φ)) ⊢ ⊥) → (Γ ⊢ φ)

  [∧]-intro : ∀{Γ}{φ ψ} → (Γ ⊢ φ) → (Γ ⊢ ψ) → (Γ ⊢ (φ ∧ ψ))
  [∧]-elimₗ : ∀{Γ}{φ ψ} → (Γ ⊢ (φ ∧ ψ)) → (Γ ⊢ φ)
  [∧]-elimᵣ : ∀{Γ}{φ ψ} → (Γ ⊢ (φ ∧ ψ)) → (Γ ⊢ ψ)

  [∨]-introₗ : ∀{Γ}{φ ψ} → (Γ ⊢ φ) → (Γ ⊢ (φ ∨ ψ))
  [∨]-introᵣ : ∀{Γ}{φ ψ} → (Γ ⊢ ψ) → (Γ ⊢ (φ ∨ ψ))
  [∨]-elim   : ∀{Γ}{φ ψ χ} → ((Γ ∪ singleton(φ)) ⊢ χ) → ((Γ ∪ singleton(ψ)) ⊢ χ) → (Γ ⊢ (φ ∨ ψ)) → (Γ ⊢ χ)

  [⟶]-intro : ∀{Γ}{φ ψ} → ((Γ ∪ singleton(φ)) ⊢ ψ) → (Γ ⊢ (φ ⟶ ψ))
  [⟶]-elim  : ∀{Γ}{φ ψ} → (Γ ⊢ φ) → (Γ ⊢ (φ ⟶ ψ)) → (Γ ⊢ ψ)

  [⟷]-intro : ∀{Γ}{φ ψ} → ((Γ ∪ singleton(ψ)) ⊢ φ) → ((Γ ∪ singleton(φ)) ⊢ ψ) → (Γ ⊢ (φ ⟷ ψ))
  [⟷]-elimₗ : ∀{Γ}{φ ψ} → (Γ ⊢ ψ) → (Γ ⊢ (φ ⟷ ψ)) → (Γ ⊢ φ)
  [⟷]-elimᵣ : ∀{Γ}{φ ψ} → (Γ ⊢ φ) → (Γ ⊢ (φ ⟷ ψ)) → (Γ ⊢ ψ)

module _ where
  private variable P : Type{ℓₚ}
  private variable Γ Γ₁ Γ₂ : Formulas(P){ℓ}
  private variable φ ψ : Formula(P)

  _⊬_ : Formulas(P){ℓ} → Formula(P) → Stmt
  _⊬_ = Meta.¬_ ∘₂ (_⊢_)

  weaken-union-singleton : (Γ₁ ⊆ Γ₂) → (((Γ₁ ∪ singleton(φ)) ⊢_) ⊆ ((Γ₂ ∪ singleton(φ)) ⊢_))

  weaken : (Γ₁ ⊆ Γ₂) → ((Γ₁ ⊢_) ⊆ (Γ₂ ⊢_))
  weaken Γ₁Γ₂ {φ}        (direct p)         = direct (Γ₁Γ₂ p)
  weaken Γ₁Γ₂ {.⊤}       [⊤]-intro          = [⊤]-intro
  weaken Γ₁Γ₂ {.⊥}       ([⊥]-intro  p q)   = [⊥]-intro  (weaken Γ₁Γ₂ p) (weaken Γ₁Γ₂ q)
  weaken Γ₁Γ₂ {φ}        ([⊥]-elim   p)     = [⊥]-elim   (weaken Γ₁Γ₂ p)
  weaken Γ₁Γ₂ {.(¬ _)}   ([¬]-intro  p)     = [¬]-intro  (weaken-union-singleton Γ₁Γ₂ p)
  weaken Γ₁Γ₂ {φ}        ([¬]-elim   p)     = [¬]-elim   (weaken-union-singleton Γ₁Γ₂ p)
  weaken Γ₁Γ₂ {.(_ ∧ _)} ([∧]-intro  p q)   = [∧]-intro  (weaken Γ₁Γ₂ p) (weaken Γ₁Γ₂ q)
  weaken Γ₁Γ₂ {φ}        ([∧]-elimₗ  p)     = [∧]-elimₗ  (weaken Γ₁Γ₂ p)
  weaken Γ₁Γ₂ {φ}        ([∧]-elimᵣ  p)     = [∧]-elimᵣ  (weaken Γ₁Γ₂ p)
  weaken Γ₁Γ₂ {.(_ ∨ _)} ([∨]-introₗ p)     = [∨]-introₗ (weaken Γ₁Γ₂ p)
  weaken Γ₁Γ₂ {.(_ ∨ _)} ([∨]-introᵣ p)     = [∨]-introᵣ (weaken Γ₁Γ₂ p)
  weaken Γ₁Γ₂ {φ}        ([∨]-elim   p q r) = [∨]-elim   (weaken-union-singleton Γ₁Γ₂ p) (weaken-union-singleton Γ₁Γ₂ q) (weaken Γ₁Γ₂ r)
  weaken Γ₁Γ₂ {.(_ ⟶ _)} ([⟶]-intro  p)     = [⟶]-intro  (weaken-union-singleton Γ₁Γ₂ p)
  weaken Γ₁Γ₂ {φ}        ([⟶]-elim   p q)   = [⟶]-elim   (weaken Γ₁Γ₂ p) (weaken Γ₁Γ₂ q)
  weaken Γ₁Γ₂ {.(_ ⟷ _)} ([⟷]-intro  p q)   = [⟷]-intro  (weaken-union-singleton Γ₁Γ₂ p) (weaken-union-singleton Γ₁Γ₂ q)
  weaken Γ₁Γ₂ {φ}        ([⟷]-elimₗ  p q)   = [⟷]-elimₗ  (weaken Γ₁Γ₂ p) (weaken Γ₁Γ₂ q)
  weaken Γ₁Γ₂ {φ}        ([⟷]-elimᵣ  p q)   = [⟷]-elimᵣ  (weaken Γ₁Γ₂ p) (weaken Γ₁Γ₂ q)

  weaken-union-singleton Γ₁Γ₂ p = weaken (Either.mapLeft Γ₁Γ₂) p

  weaken-union : (Γ₁ ⊢_) ⊆ ((Γ₁ ∪ Γ₂) ⊢_)
  weaken-union = weaken Either.Left

  [⟵]-intro : ((Γ ∪ singleton(φ)) ⊢ ψ) → (Γ ⊢ (ψ ⟵ φ))
  [⟵]-intro = [⟶]-intro

  [⟵]-elim : (Γ ⊢ φ) → (Γ ⊢ (ψ ⟵ φ)) → (Γ ⊢ ψ)
  [⟵]-elim = [⟶]-elim

  [¬¬]-elim : (Γ ⊢ ¬(¬ φ)) → (Γ ⊢ φ)
  [¬¬]-elim nnφ =
    ([¬]-elim
      ([⊥]-intro
        (direct(Right [≡]-intro))
        (weaken-union nnφ)
      )
    )

  [¬¬]-intro : (Γ ⊢ φ) → (Γ ⊢ ¬(¬ φ))
  [¬¬]-intro Γφ =
    ([¬]-intro
      ([⊥]-intro
        (weaken-union Γφ)
        (direct (Right [≡]-intro))
      )
    )

