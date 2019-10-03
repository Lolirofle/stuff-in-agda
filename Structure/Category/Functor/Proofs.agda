module Structure.Category.Functor.Proofs where

import      Lvl
open import Sets.Setoid
open import Structure.Category
open import Structure.Category.Functor
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
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
  (F : Functor(Categoryₗ)(Categoryᵣ))
  ⦃ map-function : ∀{x y} → Function(Functor.map(F) {x}{y}) ⦄
  where

  open SideNotation(Categoryₗ)(Categoryᵣ)
  open Functor(F)
  open module Equivₗ {x}{y} = Equivalence ([≡]-equivalence ⦃ morphism-equivₗ{x}{y} ⦄) using () renaming (transitivity to transitivityₗ ; symmetry to symmetryₗ ; reflexivity to reflexivityₗ)
  open module Equivᵣ {x}{y} = Equivalence ([≡]-equivalence ⦃ morphism-equivᵣ{x}{y} ⦄) using () renaming (transitivity to transitivityᵣ ; symmetry to symmetryᵣ ; reflexivity to reflexivityᵣ)

  isomorphism-preserving : ∀{x y}{f : x ⟶ₗ y} → Category.Isomorphism(Categoryₗ)(f) → Category.Isomorphism(Categoryᵣ)(map f)
  isomorphism-preserving {x}{y} {f} (Category.Isomorphism.intro g gfid fgid) = Category.Isomorphism.intro (map g) proofₗ proofᵣ where
    proofₗ : map(g) ∘ᵣ map(f) ≡ idᵣ
    proofₗ =
      (symmetry(_≡_) op-preserving  :of: (map(g) ∘ᵣ map(f) ≡ map(g ∘ₗ f)))
      🝖 ([≡]-with(map) gfid         :of: (_                ≡ map(idₗ)))
      🝖 (id-preserving              :of: (_                ≡ idᵣ))

    proofᵣ : map(f) ∘ᵣ map(g) ≡ idᵣ
    proofᵣ =
      (symmetry(_≡_) op-preserving  :of: (map(f) ∘ᵣ map(g) ≡ map(f ∘ₗ g)))
      🝖 ([≡]-with(map) fgid         :of: (_                ≡ map(idₗ)))
      🝖 (id-preserving              :of: (_                ≡ idᵣ))
