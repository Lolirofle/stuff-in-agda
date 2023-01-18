module Structure.Operator.Signature where

open import Data
open import Data.Tuple
open import Data.Tuple.Raise
open import Data.Tuple.Raiseᵣ.Functions as Raise
open import Data.Tuple.RaiseTypeᵣ.Functions as RaiseType
open import Function.Multi
import      Lvl
import      Lvl.MultiFunctions as Lvl
open import Numeral.Finite
open import Numeral.Natural
open import Type
open import Type.Dependent.Sigma

record Signature : Type{Lvl.𝟎} where
  field
    ty  : ℕ
    fn  : ℕ
    rel : ℕ
    Function : (Σ ℕ (𝕟(ty) ^_) ⨯ 𝕟(ty)) ^ fn
    Relation : (Σ ℕ (𝕟(ty) ^_)) ^ rel

{- TODO
module _ (s : Signature) {ℓᵥ} (V : 𝕟(Signature.ty s) → Type{ℓᵥ}) where
  open Signature(s)

  -- {-# POSITIVE #-}
  data Term : 𝕟(ty) → Type{ℓᵥ} where
    var : ∀(t) → V(t) → Term(t)
    _$_ : (f : 𝕟(fn)) → let (intro _ dom , codom) = Raise.index f(Function) in RaiseType.reduceOrᵣ(_⨯_) (Unit{ℓᵥ}) (RaiseType.mapFromRaise Term dom) → Term(codom)
    -- _$_ : (f : 𝕟(fn)) → let (intro _ dom , codom) = Raise.index f(Function) in Term codom → Term(codom)

  data Language : Type{ℓᵥ} where
    _$ᵣₑₗ_ : (r : 𝕟(rel)) → {!!} → Language
    _≡_ : ∀{t} → Term(t) → Term(t) → Language
-}

module TypeInterpretation
  (s : Signature)
  {ℓ𝓈 : 𝕟(Signature.ty s) → Lvl.Level}
  {ℓᵣ𝓈 : Lvl.Level ^ (Signature.rel s)}
  (Domains : (i : 𝕟(Signature.ty s)) → Type{ℓ𝓈(i)})
  where
  open Signature(s)

  FunctionsType : Type
  FunctionsType = Raise.elimDep
    {ℓ = \n l → Lvl.𝐒(Lvl.⨆{n = n}(Raise.map{n = n}(\(intro args dom , codom) → ℓ𝓈(codom) Lvl.⊔ Lvl.⨆(Raise.map ℓ𝓈 dom)) l))}
    (\_ _ → Type{_})
    Unit
    f
    (\x _ → f x ⨯_)
    {fn}
    Function
    where
      f = \(intro args dom , codom) → RaiseType.mapFromRaise Domains(dom) ⇉ Domains(codom)

  RelationsType : Type
  RelationsType = Raise.elimDep
    {ℓ = \n l → Lvl.𝐒 (Lvl.⨆{n = n} (Raise.map{n = n} (\(intro args dom , ℓ) → Lvl.𝐒(ℓ) Lvl.⊔ Lvl.⨆(Raise.map ℓ𝓈 dom)) l))}
    (\_ _ → Type{_})
    Unit
    f
    (\x _ → f x ⨯_)
    {rel}
    (Raise.transpose₂ Relation ℓᵣ𝓈)
    where
      f = \(intro args dom , ℓ) → RaiseType.mapFromRaise Domains(dom) ⇉ Type{ℓ}

  record Structure : Type{Lvl.of(FunctionsType) Lvl.⊔ Lvl.of(RelationsType)} where
    field
      functions : FunctionsType
      relations : RelationsType
      -- TODO: And the axioms. Use an interpretation of Language like how FunctionsType is an interpretation of Function

  -- TODO: Define Homomorphism for Structure
