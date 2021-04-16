module Formalization.ClassicalPropositionalLogic.Place where

open import Data.Boolean
open import Data.Tuple as Tuple using (_,_ ; _⨯_)
import      Lvl
open import Formalization.ClassicalPropositionalLogic.Syntax
open import Functional as Fn using (_∘_ ; const)
open import Sets.PredicateSet using (PredSet)
open import Type

private variable ℓₚ ℓᵢ ℓ : Lvl.Level
private variable T A B I : Type{ℓ}
private variable f : A → B

module _ (P : Type{ℓₚ}) where
  private variable s e : Bool
  private variable p : P
  private variable φ ψ γ : Formula(P)

  record Index(I : Type{ℓ}) : Type{ℓ} where
    field
      id : I
      ∧ₗ : I → I
      ∧ᵣ : I → I
      ∨ₗ : I → I
      ∨ᵣ : I → I
      ⟶ₗ : I → I
      ⟶ᵣ : I → I
      
      ∧ₗ₀ : I → I
      ∧ᵣ₀ : I → I
      ∨ₗ₀ : I → I
      ∨ᵣ₀ : I → I
      ⟶ₗ₀ : I → I
      ⟶ᵣ₀ : I → I

  module _ (ind : Index(I)) where
    private variable i : I

    data Context : I → (Formula(P) → Formula(P)) → Type{Lvl.of(I) Lvl.⊔ ℓₚ} where
      identity     : Context(Index.id ind) Fn.id
      conjunctionₗ : Context(Index.∧ₗ₀ ind i) f → Context(Index.∧ₗ ind i) ((φ ∧_) ∘ f)
      conjunctionᵣ : Context(Index.∧ᵣ₀ ind i) f → Context(Index.∧ᵣ ind i) ((_∧ φ) ∘ f)
      disjunctionₗ : Context(Index.∨ₗ₀ ind i) f → Context(Index.∨ₗ ind i) ((φ ∨_) ∘ f)
      disjunctionᵣ : Context(Index.∨ᵣ₀ ind i) f → Context(Index.∨ᵣ ind i) ((_∨ φ) ∘ f)
      implicationₗ : Context(Index.⟶ₗ₀ ind i) f → Context(Index.⟶ₗ ind i) ((φ ⟶_) ∘ f)
      implicationᵣ : Context(Index.⟶ᵣ₀ ind i) f → Context(Index.⟶ᵣ ind i) ((_⟶ φ) ∘ f)

  Place : Bool → Bool → (Formula(P) → Formula(P)) → Type
  Place s e = Context index (s , e) where
    index : Index(Bool ⨯ Bool)
    Index.id index = (𝑇 , e)
    Index.∧ₗ index = Fn.id
    Index.∧ᵣ index = Fn.id
    Index.∨ₗ index = Fn.id
    Index.∨ᵣ index = Fn.id
    Index.⟶ₗ index = Fn.id
    Index.⟶ᵣ index = Tuple.map Fn.id (const 𝑇)
    Index.∧ₗ₀ index = Fn.id
    Index.∧ᵣ₀ index = Fn.id
    Index.∨ₗ₀ index = Fn.id
    Index.∨ᵣ₀ index = Fn.id
    Index.⟶ₗ₀ index = Fn.id
    Index.⟶ᵣ₀ index = Tuple.map not (const 𝑇)
  {-
  -- (Place s e F φ) means that the formula F lies on a (strictly (e = 𝐹) / not strictly (e = 𝑇)) (positive (s = 𝑇) / negative (s = 𝐹)) position in the formula φ.
  -- Also called: Occurrence, part, (strictly) positive/negative subformula.
  data Place : Bool → Bool → Formula(P) → Formula(P) → Type{ℓₚ} where
    refl         : Place 𝑇 e φ φ
    conjunctionₗ : Place s e γ φ       → Place s e γ (φ ∧ ψ)
    conjunctionᵣ : Place s e γ ψ       → Place s e γ (φ ∧ ψ)
    disjunctionₗ : Place s e γ φ       → Place s e γ (φ ∨ ψ)
    disjunctionᵣ : Place s e γ ψ       → Place s e γ (φ ∨ ψ)
    implicationₗ : Place (not s) e γ φ → Place s 𝑇 γ (φ ⟶ ψ)
    implicationᵣ : Place s e γ ψ       → Place s e γ (φ ⟶ ψ)
  -}

  StrictlyPositive = Place 𝑇 𝐹
  StrictlyNegative = Place 𝐹 𝐹
  Positive         = Place 𝑇 𝑇
  Negative         = Place 𝐹 𝑇

  strictly-negative-to-strictly-positive : Place 𝐹 𝐹 f → Place 𝑇 𝐹 f
  strictly-negative-to-strictly-positive (conjunctionₗ p) = conjunctionₗ (strictly-negative-to-strictly-positive p)
  strictly-negative-to-strictly-positive (conjunctionᵣ p) = conjunctionᵣ (strictly-negative-to-strictly-positive p)
  strictly-negative-to-strictly-positive (disjunctionₗ p) = disjunctionₗ (strictly-negative-to-strictly-positive p)
  strictly-negative-to-strictly-positive (disjunctionᵣ p) = disjunctionᵣ (strictly-negative-to-strictly-positive p)
  strictly-negative-to-strictly-positive (implicationₗ p) = implicationₗ (strictly-negative-to-strictly-positive p)

  strictly-to-not-strictly : Place s 𝐹 f → Place s 𝑇 f
  strictly-to-not-strictly identity         = identity
  strictly-to-not-strictly (conjunctionₗ p) = conjunctionₗ (strictly-to-not-strictly p)
  strictly-to-not-strictly (conjunctionᵣ p) = conjunctionᵣ (strictly-to-not-strictly p)
  strictly-to-not-strictly (disjunctionₗ p) = disjunctionₗ (strictly-to-not-strictly p)
  strictly-to-not-strictly (disjunctionᵣ p) = disjunctionᵣ (strictly-to-not-strictly p)
  strictly-to-not-strictly (implicationₗ p) = implicationₗ (strictly-to-not-strictly p)
