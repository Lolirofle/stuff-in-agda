open import Formalization.PredicateLogic.Signature

module Formalization.PredicateLogic.Classical.NaturalDeduction (𝔏 : Signature) where
open Signature(𝔏)

open import Data.ListSized
import      Lvl
open import Formalization.PredicateLogic.Syntax(𝔏)
open import Formalization.PredicateLogic.Syntax.Substitution(𝔏)
open import Functional using (_∘_ ; _∘₂_ ; swap)
open import Numeral.Finite
open import Numeral.Natural
open import Relator.Equals.Proofs.Equiv
open import Sets.PredicateSet using (PredSet ; _∈_ ; _∉_ ; _∪_ ; _∪•_ ; _∖_ ; _⊆_ ; _⊇_ ; ∅ ; [≡]-to-[⊆] ; [≡]-to-[⊇]) renaming (•_ to · ; _≡_ to _≡ₛ_)
open import Type

private variable ℓ : Lvl.Level
private variable args vars : ℕ
private variable Γ : PredSet{ℓ}(Formula(vars))

data _⊢_ {ℓ} : PredSet{ℓ}(Formula(vars)) → Formula(vars) → Type{Lvl.𝐒(ℓₚ Lvl.⊔ ℓₒ Lvl.⊔ ℓ)} where
  direct : (Γ ⊆ (Γ ⊢_))

  [⊤]-intro : (Γ ⊢ ⊤)

  [⊥]-elim  : ∀{φ} → ((Γ ∪ ·(¬ φ)) ⊢ ⊥) → (Γ ⊢ φ)

  [∧]-intro : ∀{φ ψ} → (Γ ⊢ φ) → (Γ ⊢ ψ) → (Γ ⊢ (φ ∧ ψ))
  [∧]-elimₗ : ∀{φ ψ} → (Γ ⊢ (φ ∧ ψ)) → (Γ ⊢ φ)
  [∧]-elimᵣ : ∀{φ ψ} → (Γ ⊢ (φ ∧ ψ)) → (Γ ⊢ ψ)

  [∨]-introₗ : ∀{φ ψ} → (Γ ⊢ φ) → (Γ ⊢ (φ ∨ ψ))
  [∨]-introᵣ : ∀{φ ψ} → (Γ ⊢ ψ) → (Γ ⊢ (φ ∨ ψ))
  [∨]-elim   : ∀{φ ψ χ} → ((Γ ∪ · φ) ⊢ χ) → ((Γ ∪ · ψ) ⊢ χ) → (Γ ⊢ (φ ∨ ψ)) → (Γ ⊢ χ)

  [⟶]-intro : ∀{φ ψ} → ((Γ ∪ · φ) ⊢ ψ) → (Γ ⊢ (φ ⟶ ψ))
  [⟶]-elim  : ∀{φ ψ} → (Γ ⊢ φ) → (Γ ⊢ (φ ⟶ ψ)) → (Γ ⊢ ψ)

  [Ɐ]-intro : ∀{φ} → (∀{t} → (Γ ⊢ (substitute0 t φ))) → (Γ ⊢ (Ɐ φ))
  [Ɐ]-elim  : ∀{φ} → (Γ ⊢ (Ɐ φ)) → ∀{t} → (Γ ⊢ (substitute0 t φ))

  [∃]-intro : ∀{φ}{t} → (Γ ⊢ (substitute0 t φ)) → (Γ ⊢ (∃ φ))
  [∃]-elim  : ∀{φ ψ} → (∀{t} → (Γ ∪ ·(substitute0 t φ)) ⊢ ψ) → (Γ ⊢ (∃ φ)) → (Γ ⊢ ψ)

module _ where
  open import Data.Either as Either
  import      Logic.Propositional as Meta
  open import Relator.Equals

  private variable Γ₁ Γ₂ : PredSet{ℓ}(Formula(vars))
  private variable φ ψ : Formula(vars)

  _⊬_ : PredSet{ℓ}(Formula(vars)) → Formula(vars) → Type
  _⊬_ = Meta.¬_ ∘₂ (_⊢_)

  [⟵]-intro : ((Γ ∪ · φ) ⊢ ψ) → (Γ ⊢ (ψ ⟵ φ))
  [⟵]-intro = [⟶]-intro

  [⟵]-elim : (Γ ⊢ φ) → (Γ ⊢ (ψ ⟵ φ)) → (Γ ⊢ ψ)
  [⟵]-elim = [⟶]-elim

  [¬]-intro : ((Γ ∪ · φ) ⊢ ⊥) → (Γ ⊢ (¬ φ))
  [¬]-intro = [⟶]-intro

  [⟷]-intro : ∀{φ ψ} → ((Γ ∪ · ψ) ⊢ φ) → ((Γ ∪ · φ) ⊢ ψ) → (Γ ⊢ (φ ⟷ ψ))
  [⟷]-intro l r = [∧]-intro ([⟶]-intro l) ([⟶]-intro r)

  [⟷]-elimₗ : ∀{φ ψ} → (Γ ⊢ ψ) → (Γ ⊢ (φ ⟷ ψ)) → (Γ ⊢ φ)
  [⟷]-elimₗ Γψ Γφψ = [⟶]-elim Γψ ([∧]-elimₗ Γφψ)

  [⟷]-elimᵣ : ∀{φ ψ} → (Γ ⊢ φ) → (Γ ⊢ (φ ⟷ ψ)) → (Γ ⊢ ψ)
  [⟷]-elimᵣ Γφ Γφψ = [⟶]-elim Γφ ([∧]-elimᵣ Γφψ)

  weaken-union-singleton : (Γ₁ ⊆ Γ₂) → (((Γ₁ ∪ · φ) ⊢_) ⊆ ((Γ₂ ∪ · φ) ⊢_))
  weaken : (Γ₁ ⊆ Γ₂) → ((Γ₁ ⊢_) ⊆ (Γ₂ ⊢_))

  weaken Γ₁Γ₂ {φ}                  (direct p)       = direct (Γ₁Γ₂ p)
  weaken Γ₁Γ₂ {.⊤}                 [⊤]-intro        = [⊤]-intro
  weaken Γ₁Γ₂ {φ}                  ([⊥]-elim p)     = [⊥]-elim (weaken-union-singleton Γ₁Γ₂ p)
  weaken Γ₁Γ₂ {.(_ ∧ _)}           ([∧]-intro p q)  = [∧]-intro (weaken Γ₁Γ₂ p) (weaken Γ₁Γ₂ q)
  weaken Γ₁Γ₂ {φ}                  ([∧]-elimₗ p)    = [∧]-elimₗ (weaken Γ₁Γ₂ p)
  weaken Γ₁Γ₂ {φ}                  ([∧]-elimᵣ p)    = [∧]-elimᵣ (weaken Γ₁Γ₂ p)
  weaken Γ₁Γ₂ {.(_ ∨ _)}           ([∨]-introₗ p)   = [∨]-introₗ (weaken Γ₁Γ₂ p)
  weaken Γ₁Γ₂ {.(_ ∨ _)}           ([∨]-introᵣ p)   = [∨]-introᵣ (weaken Γ₁Γ₂ p)
  weaken Γ₁Γ₂ {φ}                  ([∨]-elim p q r) = [∨]-elim (weaken-union-singleton Γ₁Γ₂ p) (weaken-union-singleton Γ₁Γ₂ q) (weaken Γ₁Γ₂ r)
  weaken Γ₁Γ₂ {.(_ ⟶ _)}           ([⟶]-intro p)    = [⟶]-intro (weaken-union-singleton Γ₁Γ₂ p)
  weaken Γ₁Γ₂ {φ}                  ([⟶]-elim p q)   = [⟶]-elim (weaken Γ₁Γ₂ p) (weaken Γ₁Γ₂ q)
  weaken Γ₁Γ₂ {.(Ɐ _)}             ([Ɐ]-intro p)    = [Ɐ]-intro (weaken Γ₁Γ₂ p)
  weaken Γ₁Γ₂ {.(substitute0 _ _)} ([Ɐ]-elim p)     = [Ɐ]-elim (weaken Γ₁Γ₂ p)
  weaken Γ₁Γ₂ {.(∃ _)}             ([∃]-intro p)    = [∃]-intro (weaken Γ₁Γ₂ p)
  weaken Γ₁Γ₂ {φ}                  ([∃]-elim p q)   = [∃]-elim (weaken-union-singleton Γ₁Γ₂ p) (weaken Γ₁Γ₂ q)
  weaken-union-singleton Γ₁Γ₂ p = weaken (Either.mapLeft Γ₁Γ₂) p

  weaken-union : (Γ₁ ⊢_) ⊆ ((Γ₁ ∪ Γ₂) ⊢_)
  weaken-union = weaken Left

  [⊥]-elim-constructive : (Γ ⊢ ⊥) → (Γ ⊢ φ)
  [⊥]-elim-constructive Γ⊥ = [⊥]-elim (weaken-union Γ⊥)

  [¬¬]-elim : (Γ ⊢ ¬(¬ φ)) → (Γ ⊢ φ)
  [¬¬]-elim nnφ =
    ([⊥]-elim
      ([⟶]-elim
        (direct(Right [≡]-intro))
        (weaken-union nnφ)
      )
    )

  [¬¬]-intro : (Γ ⊢ φ) → (Γ ⊢ ¬(¬ φ))
  [¬¬]-intro Γφ =
    ([¬]-intro
      ([⟶]-elim
        (weaken-union Γφ)
        (direct (Right [≡]-intro))
      )
    )
