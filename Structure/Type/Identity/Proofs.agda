module Structure.Type.Identity.Proofs where

import      Lvl
open import Logic
open import Logic.Propositional
open import Structure.Relator
open import Structure.Relator.Properties
open import Structure.Setoid
open import Structure.Type.Identity
open import Type
open import Type.Properties.MereProposition

private variable ℓ ℓₑ ℓₘₑ ℓₚ : Lvl.Level

-- The elimination rules are equivalent to their alternative forms with a fixed parameter.
module _ {T : Type{ℓ}} (Id : T → T → Stmt{ℓₑ}) ⦃ refl : Reflexivity(Id) ⦄ where
  idKElim-from-fixed : Names.IdentityKEliminator Id {ℓₚ} ← Names.IdentityKEliminatorAlt Id {ℓₚ}
  idKElim-from-fixed = \K P p id → K(P) p id

  idKElim-to-fixed : Names.IdentityKEliminator Id {ℓₑ Lvl.⊔ Lvl.𝐒(ℓₚ)} → Names.IdentityKEliminatorAlt Id {ℓₚ}
  idKElim-to-fixed{ℓₚ} = \K P p id → K(\{x} id → (P : (Id x x) → Stmt) → P(reflexivity(Id) {x}) → P(id)) (\_ p → p) id P p

  idElim-from-fixedᵣ : Names.IdentityEliminator Id {ℓₚ} ← Names.IdentityEliminatorAltᵣ Id {ℓₚ}
  idElim-from-fixedᵣ = \J P p id → J(P) p id

  idElim-to-fixedᵣ : Names.IdentityEliminator Id {ℓ Lvl.⊔ ℓₑ Lvl.⊔ Lvl.𝐒(ℓₚ)} → Names.IdentityEliminatorAltᵣ Id {ℓₚ}
  idElim-to-fixedᵣ = \J P p id → J(\{x}{y} id → (P : ∀{y} → (Id x y) → Stmt) → P(reflexivity(Id) {x}) → P(id)) (\_ p → p) id P p

  idElim-from-fixedₗ : Names.IdentityEliminator Id {ℓₚ} ← Names.IdentityEliminatorAltₗ Id {ℓₚ}
  idElim-from-fixedₗ = \J P p id → J(P) p id

  idElim-to-fixedₗ : Names.IdentityEliminator Id {ℓ Lvl.⊔ ℓₑ Lvl.⊔ Lvl.𝐒(ℓₚ)} → Names.IdentityEliminatorAltₗ Id {ℓₚ}
  idElim-to-fixedₗ = (\J P p id → J(\{x}{y} id → (P : ∀{x} → (Id x y) → Stmt) → P(reflexivity(Id) {y}) → P(id)) (\_ p → p) id P p)

  -----------------------------------------------------------------------------
  -- Convenience functions.
  -- Use like `idElim` and `idKElim`.

  idKElimFixed : ⦃ IdentityKEliminator Id ⦄ → Names.IdentityKEliminatorAlt Id {ℓₚ}
  idKElimFixed = idKElim-to-fixed(idKElim(Id))

  idElimFixedᵣ : ⦃ IdentityEliminator Id ⦄ → Names.IdentityEliminatorAltᵣ Id {ℓₚ}
  idElimFixedᵣ = idElim-to-fixedᵣ(idElim(Id))

  idElimFixedₗ : ⦃ IdentityEliminator Id ⦄ → Names.IdentityEliminatorAltₗ Id {ℓₚ}
  idElimFixedₗ = idElim-to-fixedₗ(idElim(Id))

-- How UIP and axiom K imply each other.
module _ (T : Type{ℓ}) ⦃ equiv-T : Equiv{ℓₑ}(T) ⦄ ⦃ equiv-eq : ∀{x y : T} → Equiv{ℓₘₑ}(x ≡ y) ⦄ where
  uip-to-idKElim : ⦃ ∀{x : T}{P : (x ≡ x) → Type{ℓₚ}} → UnaryRelator(P) ⦄ → ⦃ UniqueIdentityProofs(T) ⦄ → IdentityKEliminator(_≡_ {T = T}) {ℓₚ}
  IdentityKEliminator.elim uip-to-idKElim P p {x} _ = substitute₁ᵣ(P) (uniqueness(x ≡ x)) p

  idKElim-to-uip : ⦃ IdentityEliminator(_≡_ {T = T}) {ℓₑ Lvl.⊔ ℓₘₑ} ⦄ → ⦃ IdentityKEliminator(_≡_ {T = T}) {ℓₑ Lvl.⊔ Lvl.𝐒(ℓₘₑ)} ⦄ → UniqueIdentityProofs(T)
  MereProposition.uniqueness idKElim-to-uip {xy₁}{xy₂} =
    idElim(_≡_ ⦃ equiv-T ⦄)
      (\{x}{y} xy₁ → (xy₂ : x ≡ y) → (xy₁ ≡ xy₂))
      (\{x} xx₁ → idKElimFixed(_≡_ ⦃ equiv-T ⦄)
        (\xx₂ → reflexivity(_≡_) ≡ xx₂)
        (reflexivity(_≡_) ⦃ Equiv.reflexivity equiv-eq ⦄)
        xx₁
      )
      xy₁
      xy₂
