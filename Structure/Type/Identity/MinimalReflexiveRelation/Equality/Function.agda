module Structure.Type.Identity.MinimalReflexiveRelation.Equality.Function where

open import Data
open import Data.Tuple using (_⨯_ ; _,_)
open import Data.Tuple.Raise
import      Data.Tuple.Raiseᵣ.Functions as Raise
open import Data.Tuple.RaiseTypeᵣ
import      Data.Tuple.RaiseTypeᵣ.Functions as RaiseType
import      Lvl
open import Functional using (_→ᶠ_ ; id ; _on₂_ ; swap ; _$_ ; apply)
open import Function.Multi
import      Function.Multi.Functions as Multi
open import Logic
open import Logic.Propositional
open import Logic.Propositional.Proofs.Structures
open import Numeral.Natural
open import Structure.Function
open import Structure.Function.Multi
open import Structure.Setoid using (Equiv ; intro) renaming (_≡_ to _≡ₛ_)
open import Structure.Relator.Equivalence
import      Structure.Relator.Names as Names
open import Structure.Relator.Properties
open import Structure.Relator.Properties.Proofs
open import Structure.Relator
open import Structure.Type.Identity
open import Structure.Type.Identity.Proofs
open import Syntax.Function
open import Type

private variable ℓ ℓ₁ ℓ₂ ℓₑ₁ ℓₑ₂ ℓₑ ℓₘₑ ℓₚ ℓₒ : Lvl.Level
private variable T A B : Type{ℓ}
private variable x y : T
private variable _≡_ _▫_ : T → T → Stmt{ℓ}

open import Structure.Type.Identity.MinimalReflexiveRelation.Equality

module _
  {ℓ𝓈ₑ : Lvl.Level → Lvl.Level}
  {B : Type{ℓ}}
  ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄
  {_≡_ : ∀{ℓ}{T : Type{ℓ}} → T → T → Stmt{ℓ𝓈ₑ(ℓ)}}
  ⦃ refl : ∀{ℓ}{T : Type{ℓ}} → Reflexivity{T = T}(_≡_) ⦄
  ⦃ minRefl : ∀{ℓₚ}{ℓ}{T : Type{ℓ}} → MinimalReflexiveRelation{ℓₚ = ℓₚ}(_≡_ {T = T}) ⦄ -- TODO: Temporary
  where

  private
    [≡]-equivs : (n : ℕ) → ∀{ℓ𝓈}{As : Types{n}(ℓ𝓈)} → RaiseType.reduceOrᵣ(_⨯_) (Unit{Lvl.𝟎}) (RaiseType.mapWithLvls (\A ℓₑ → Equiv{ℓₑ}(A)) As (Raise.map ℓ𝓈ₑ(ℓ𝓈)))
    [≡]-equivs 0 = <>
    [≡]-equivs 1 = minimal-reflection-to-equiv
    [≡]-equivs (𝐒(𝐒 n)) = (minimal-reflection-to-equiv , [≡]-equivs(𝐒(n)))

  minimal-reflection-to-function₊ : (n : ℕ) → ∀{ℓ𝓈}{As : Types{n}(ℓ𝓈)} → (f : As ⇉ B) → Multi.applyTuple(n) ([≡]-equivs n) (Multi.inst-to-expl(n) (Names.Function(n))) ⦃ equiv-B ⦄ f
  minimal-reflection-to-function₊ 0        _ = reflexivity(_≡ₛ_)
  minimal-reflection-to-function₊ 1        f = congruence₁ ⦃ _ ⦄ (f) ⦃ minimal-reflection-to-function ⦄
  minimal-reflection-to-function₊ (𝐒(𝐒 n)) f = {!!}

  -- minimal-reflection-to-function₊ : ∀{n}{ℓ𝓈 ℓ𝓈ₑ}{As : Types{n}(ℓ𝓈)}{f : As ⇉ B} → Multi.quantifier₊ᵢₙₛₜ(n) {!!} (Multi.composeᵢₙₛₜ(n) (apply f) (Names.Function₊ ⦃ equiv-B = equiv-B ⦄ (n) {ℓ𝓈ₑ = ℓ𝓈ₑ} {As = As}))
  {-minimal-reflection-to-function₊ {0}       {f = f} = reflexivity(_≡ₛ_)
  minimal-reflection-to-function₊ {1}       {f = f} = congruence₁(f) ⦃ minimal-reflection-to-function ⦃ minRefl = {!!} ⦄ ⦄
  minimal-reflection-to-function₊ {𝐒(𝐒(n))} {f = f} = {!!}
-}
