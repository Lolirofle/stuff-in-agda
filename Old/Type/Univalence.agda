import      Lvl
open import Type

module Type.Univalence where

open import Functional
import      Logic.Predicate
import      Relator.Equals
import      Relator.Equals.Proofs
import      Type.Cardinality
import      Type.Cardinality.Proofs
import      Type.Functions
import      Type.Functions.Inverse

module _ {ℓₗ ℓₒ : Lvl.Level} where
  open Logic.Predicate
  open Relator.Equals{ℓₗ Lvl.⊔ ℓₒ}{Lvl.𝐒(ℓₒ)}
  open Type.Cardinality {ℓₗ}
  open Type.Cardinality.Proofs {ℓₗ}
  open Type.Functions

  UnivalenceAxiom : Type{ℓₗ Lvl.⊔ Lvl.𝐒(ℓₒ)}
  UnivalenceAxiom = ∀{X Y : Type{ℓₒ}} → Bijective{ℓₗ Lvl.⊔ Lvl.𝐒(ℓₒ)} ([≡]-to-[≍] {ℓₒ} {X}{Y})

module _ {ℓₗ ℓₒ : Lvl.Level} {univalence : UnivalenceAxiom} where
  open Logic.Predicate
  open Relator.Equals
  open Relator.Equals.Proofs
  open Type.Cardinality
  open Type.Cardinality.Proofs
  open Type.Functions.Inverse

  instance
    [≡][≍]-bijection : ∀{X Y} → ((X ≡ Y) ≍ (X ≍ Y))
    [≡][≍]-bijection {X}{Y} = [∃]-intro ([≡]-to-[≍] {ℓₗ}{ℓₒ} {X}{Y}) ⦃ univalence{X}{Y} ⦄

  [≍]-to-[≡] : ∀{X Y : Type{ℓₒ}} → (X ≍ Y) → (X ≡ Y)
  [≍]-to-[≡] {X}{Y} = inv([≡]-to-[≍] {ℓₗ}{ℓₒ} {X}{Y}) ⦃ univalence {X}{Y} ⦄

module _ {ℓₗ ℓₒ₁ ℓₒ₂ : Lvl.Level} {univalence : UnivalenceAxiom {ℓₗ Lvl.⊔ Lvl.𝐒(ℓₒ₁)}{ℓₒ₁}} where
  open Logic.Predicate
  open Relator.Equals
  open Relator.Equals.Proofs
  open Type.Cardinality {ℓₗ Lvl.⊔ Lvl.𝐒(ℓₒ₁)}
  open Type.Cardinality.Proofs {ℓₗ Lvl.⊔ Lvl.𝐒(ℓₒ₁)}
  open Type.Functions

  _≡₂_ = _≡_ {ℓₗ}{ℓₒ₂}
  _≡ₗ_ = _≡_ {ℓₗ}

  -- For any type function P from an universe Type{ℓₒ₁} to Type{ℓₒ₂}
  -- where subst, a substitution for P holds using (_≍_)
  -- and where the substitution by reflexivity using (_≍_) gives the exact same proof (is a identity function),
  -- then this substitution will give the same results as the standard substitution rule for equalities (_≡_) for this P.
  postulate transport-theorem : ∀{P : Type{ℓₒ₁} → Type{ℓₒ₂}}
                      → (subst : (∀{X Y} → (X ≍ Y) → P(X) → P(Y)))
                      → (subst-id : (∀{X} → (px : P(X)) → (subst([≍]-reflexivity) (px) ≡₂ px)))
                      → ∀{X Y}
                      → (xy : (X ≍ Y))
                      → (px : P(X))
                      → (subst(xy) (px) ≡₂ [≡]-substitutionᵣ {ℓₗ Lvl.⊔ Lvl.𝐒(ℓₒ₁)}{Lvl.𝐒(ℓₒ₁)} ([≍]-to-[≡] {ℓₗ Lvl.⊔ Lvl.𝐒(ℓₒ₁)}{ℓₒ₁} {univalence} (xy)) {P} px)
  -- transport-theorem {P} (subst) (subst-id) ([∃]-intro bijection ⦃ bijective ⦄) px =
    -- subst(xy) (px)
    -- = subst(inv bijection (bijection xy)) (px)
    -- = [≡]-substitutionᵣ (bijection xy) {P} (px)

  postulate substitution-is-bijective : ∀{P : Type{ℓₒ₁} → Type{ℓₒ₂}}
                      → (subst : (∀{X Y} → (X ≍ Y) → P(X) → P(Y)))
                      → (subst-id : (∀{X} → (px : P(X)) → (subst([≍]-reflexivity) (px) ≡₂ px)))
                      → ∀{X Y}{xy : (X ≍ Y)} → Bijective{ℓₗ Lvl.⊔ Lvl.𝐒(ℓₒ₂)} (subst(xy))

  -- TODO: univalence should probably have other level parameters from this point on

  postulate [∘]ₗ-bijective : ∀{ℓₒ₃}{X : Type{ℓₒ₁}}{Y : Type{ℓₒ₂}}{Z : Type{ℓₒ₃}}{g : X → Y} → Bijective{ℓₗ}(g) → Bijective{ℓₗ}(\(f : Y → Z) → f ∘ g)

  postulate [∘]ₗ-cancellationᵣ : ∀{ℓₒ₃}{X : Type{ℓₒ₁}}{Y : Type{ℓₒ₂}}{Z : Type{ℓₒ₃}}{f g : Y → Z}{h : X → Y} → Bijective{ℓₗ}(h) → (f ∘ h ≡ₗ  g ∘ h) → (f ≡ₗ g)

  -- subst{T} P {x}{y} xy fx = [≡]-substitutionᵣ{T}{x}{y} (xy) {P} fx
