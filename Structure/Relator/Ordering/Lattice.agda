module Structure.Relator.Ordering.Lattice where

import      Lvl
open import Functional
open import Logic
open import Logic.Propositional hiding (⊤ ; ⊥)
open import Logic.Predicate
open import Logic.Propositional.Theorems
open import Structure.Relator.Ordering
open import Structure.Relator.Properties hiding (antisymmetry ; asymmetry ; transitivity ; reflexivity ; irreflexivity)
open import Type

private variable ℓ₁ ℓ₂ ℓ₃ : Lvl.Level

module _ {T : Type{ℓ₁}} (_≤_ : T → T → Stmt{ℓ₂}) where
  record Bottom (P : T → Stmt{ℓ₃}) (m : T) : Stmt{ℓ₁ Lvl.⊔ ℓ₂ ⊔ ℓ₃} where
    constructor intro
    field
      ⦃ membership ⦄ : P(m)
      proof : ∀{x : T} → ⦃ _ : P(x) ⦄ → (m ≤ x)

  record Top (P : T → Stmt{ℓ₃}) (m : T) : Stmt{ℓ₁ Lvl.⊔ ℓ₂ ⊔ ℓ₃} where
    constructor intro
    field
      ⦃ membership ⦄ : P(m)
      proof : ∀{x : T} → ⦃ _ : P(x) ⦄ → (x ≤ m)

  record LeftBound (P : T → Stmt{ℓ₃}) (b : T) : Stmt{ℓ₁ Lvl.⊔ ℓ₂ ⊔ ℓ₃} where
    constructor intro
    field proof : ∀{x : T} → ⦃ _ : P(x) ⦄ → (b ≤ x)

  record RightBound (P : T → Stmt{ℓ₃}) (b : T) : Stmt{ℓ₁ Lvl.⊔ ℓ₂ ⊔ ℓ₃} where
    constructor intro
    field proof : ∀{x : T} → ⦃ _ : P(x) ⦄ → (x ≤ b)

  record Join (P : T → Stmt{ℓ₃}) (sup : T) : Stmt{ℓ₁ Lvl.⊔ ℓ₂ ⊔ ℓ₃} where
    constructor intro
    field
      bound : RightBound(P) (sup)
      extreme : LeftBound(RightBound(P)) (sup)

  record Meet (P : T → Stmt{ℓ₃}) (inf : T) : Stmt{ℓ₁ Lvl.⊔ ℓ₂ ⊔ ℓ₃} where
    constructor intro
    field
      bound : LeftBound(P) (inf)
      extreme : RightBound(LeftBound(P)) (inf)

  module Complete {ℓ₃} where
    record JoinSemilattice : Stmt{ℓ₁ Lvl.⊔ ℓ₂ ⊔ Lvl.𝐒(ℓ₃)} where
      constructor intro
      field proof : ∀{P : T → Stmt{ℓ₃}} → ∃(Join(P))

    record MeetSemilattice : Stmt{ℓ₁ Lvl.⊔ ℓ₂ ⊔ Lvl.𝐒(ℓ₃)} where
      constructor intro
      field proof : ∀{P : T → Stmt{ℓ₃}} → ∃(Meet(P))

    record Lattice : Stmt{ℓ₁ Lvl.⊔ ℓ₂ ⊔ Lvl.𝐒(ℓ₃)} where
      constructor intro
      field
        ⦃ meet-semilattice ⦄ : MeetSemilattice
        ⦃ join-semilattice ⦄ : JoinSemilattice

      record Bounded (⊤ : T) (⊥ : T) : Stmt{ℓ₁ Lvl.⊔ ℓ₂ ⊔ Lvl.𝐒(ℓ₃)} where
        constructor intro
        field
          ⦃ bottom ⦄ : Weak.Properties.Extremumᵣ(_≤_)(⊥)
          ⦃ top ⦄    : Weak.Properties.Extremumᵣ(_≤_)(⊤)

  bottom : (P : T → Stmt{ℓ₃}) → ⦃ _ : ∃(Bottom(P)) ⦄ → T
  bottom(P) ⦃ e ⦄ = [∃]-witness e

  top : (P : T → Stmt{ℓ₃}) → ⦃ _ : ∃(Top(P)) ⦄ → T
  top(P) ⦃ e ⦄ = [∃]-witness e

  join : (P : T → Stmt{ℓ₃}) → ⦃ _ : ∃(Join(P)) ⦄ → T
  join _ ⦃ e ⦄ = [∃]-witness e
  
  meet : (P : T → Stmt{ℓ₃}) → ⦃ _ : ∃(Meet(P)) ⦄ → T
  meet _ ⦃ e ⦄ = [∃]-witness e

  module Oper where
    ⊥ = bottom
    ⊤ = top
    ⋁ = join
    ⋀ = meet

  module LE where
    Minimum    = Bottom
    Maximum    = Top
    LowerBound = LeftBound
    UpperBound = RightBound
    Supremum   = Join
    Infimum    = Meet

    module Minimum    = Bottom
    module Maximum    = Top
    module LowerBound = LeftBound
    module UpperBound = RightBound
    module Supremum   = Join
    module Infimum    = Meet

    min = bottom
    max = top
    sup = join
    inf = meet

-- TODO: https://en.wikipedia.org/wiki/Map_of_lattices
