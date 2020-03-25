module Structure.Category.Functor.Proofs where

open import Data.Tuple as Tuple using (_,_)
open import Functional using (_$_)
open import Logic.Predicate
import      Lvl
open import Sets.Setoid
open import Structure.Category
open import Structure.Category.Properties
open import Structure.Category.Functor
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Syntax.Transitivity
open import Type

module _
  {ℓₒₗ ℓₒᵣ ℓₘₗ ℓₘᵣ : Lvl.Level}
  {Objₗ : Type{ℓₒₗ}}
  {Objᵣ : Type{ℓₒᵣ}}
  {Morphismₗ : Objₗ → Objₗ → Type{ℓₘₗ}}
  {Morphismᵣ : Objᵣ → Objᵣ → Type{ℓₘᵣ}}
  ⦃ morphism-equivₗ : ∀{x y} → Equiv(Morphismₗ x y) ⦄
  ⦃ morphism-equivᵣ : ∀{x y} → Equiv(Morphismᵣ x y) ⦄
  {Categoryₗ : Category(Morphismₗ)}
  {Categoryᵣ : Category(Morphismᵣ)}
  (F : Objₗ → Objᵣ)
  ⦃ functor : Functor(Categoryₗ)(Categoryᵣ)(F) ⦄
  where

  open Category.ArrowNotation ⦃ … ⦄
  open Category ⦃ … ⦄
  open Functor(functor)
  private open module Equivₗ {x}{y} = Equivalence ([≡]-equivalence ⦃ morphism-equivₗ{x}{y} ⦄) using () renaming (transitivity to transitivityₗ ; symmetry to symmetryₗ ; reflexivity to reflexivityₗ)
  private open module Equivᵣ {x}{y} = Equivalence ([≡]-equivalence ⦃ morphism-equivᵣ{x}{y} ⦄) using () renaming (transitivity to transitivityᵣ ; symmetry to symmetryᵣ ; reflexivity to reflexivityᵣ)

  private instance _ = Categoryₗ
  private instance _ = Categoryᵣ

  private variable x y : Objₗ

  isomorphism-preserving : ∀{f : x ⟶ y} → Morphism.Isomorphism ⦃ \{x y} → morphism-equivₗ {x}{y} ⦄ (_∘_)(id)(f) → Morphism.Isomorphism ⦃ \{x y} → morphism-equivᵣ {x}{y} ⦄ (_∘_)(id)(map f)
  ∃.witness (isomorphism-preserving ([∃]-intro g)) = map g
  ∃.proof (isomorphism-preserving {f = f} iso@([∃]-intro g)) =
    (Morphism.intro $
      map g ∘ map f 🝖-[ op-preserving ]-sym
      map(g ∘ f)    🝖-[ [≡]-with(map) (inverseₗ(f)(g) ⦃ inverse-left ⦃ iso ⦄ ⦄) ]
      map id        🝖-[ id-preserving ]
      id            🝖-end
    ) , (Morphism.intro $
      map f ∘ map g 🝖-[ op-preserving ]-sym
      map(f ∘ g)    🝖-[ [≡]-with(map) (inverseᵣ(f)(g) ⦃ inverse-right ⦃ iso ⦄ ⦄) ]
      map id        🝖-[ id-preserving ]
      id            🝖-end
    )
    where
      open Morphism.OperModule (\{x : Objₗ} → _∘_ {x = x})
      open Morphism.IdModule   (\{x : Objₗ} → _∘_ {x = x})(id)
      open Morphism.Isomorphism(\{x : Objₗ} → _∘_ {x = x})(id)(f)
