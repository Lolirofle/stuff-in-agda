module Structure.Categorical.Functor.Properties where

open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Data.Tuple.Raiseᵣ using (_^_)
open import Functional using (_→ᶠ_ ; _on₂_)
import      Lvl
open import Logic
open import Numeral.Natural
open import Structure.IndexedOperator
import      Structure.IndexedOperator.Properties.Preserving as Indexed
open import Structure.Setoid
open import Type

private variable ℓ ℓₒ ℓₘ ℓₘ₁ ℓₘ₂ ℓₑ ℓₑ₁ ℓₑ₂ : Lvl.Level
private variable Obj Obj₁ Obj₂ : Type{ℓₒ}
private variable a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ e₁ e₂ f₁ f₂ g₁ g₂ h₁ h₂ i₁ i₂ j₁ j₂ : Obj

module _
  (_⟶₁_ : Obj₁ → Obj₁ → Stmt{ℓₘ₁})
  (_⟶₂_ : Obj₂ → Obj₂ → Stmt{ℓₘ₂})
  ⦃ morphism-equiv₂ : ∀{x y} → Equiv{ℓₑ₂}(x ⟶₂ y) ⦄
  where

  private variable F : Obj₁ → Obj₂

  module Names where
    PreservingSignature = \n S F → Indexed.Names.PreservingSignature(Tuple.uncurry(_⟶₁_)) (Tuple.uncurry(_⟶₂_)) ⦃ morphism-equiv₂ ⦄ n S (Tuple.map F F)

    Preserving : (n : ℕ) → {S : (Obj₁ ⨯ Obj₁) ^ 𝐒(n)} → {F : Obj₁ → Obj₂} → PreservingSignature n S F
    Preserving n = Indexed.Names.Preserving(Tuple.uncurry(_⟶₁_)) (Tuple.uncurry(_⟶₂_)) n

    Preserving₀ : PreservingSignature 0 (a₁ , a₂) F
    Preserving₀ = Preserving 0

    Preserving₁ : PreservingSignature 1 ((a₁ , a₂) , (b₁ , b₂)) F
    Preserving₁ = Preserving 1

    Preserving₂ : PreservingSignature 2 ((a₁ , a₂) , (b₁ , b₂) , (c₁ , c₂)) F
    Preserving₂ = Preserving 2

    Preserving₃ : PreservingSignature 3 ((a₁ , a₂) , (b₁ , b₂) , (c₁ , c₂) , (d₁ , d₂)) F
    Preserving₃ = Preserving 3

    Preserving₄ : PreservingSignature 4 ((a₁ , a₂) , (b₁ , b₂) , (c₁ , c₂) , (d₁ , d₂) , (e₁ , e₂)) F
    Preserving₄ = Preserving 4

    Preserving₅ : PreservingSignature 5 ((a₁ , a₂) , (b₁ , b₂) , (c₁ , c₂) , (d₁ , d₂) , (e₁ , e₂) , (f₁ , f₂)) F
    Preserving₅ = Preserving 5

    Preserving₆ : PreservingSignature 6 ((a₁ , a₂) , (b₁ , b₂) , (c₁ , c₂) , (d₁ , d₂) , (e₁ , e₂) , (f₁ , f₂) , (g₁ , g₂)) F
    Preserving₆ = Preserving 6

    Preserving₇ : PreservingSignature 7 ((a₁ , a₂) , (b₁ , b₂) , (c₁ , c₂) , (d₁ , d₂) , (e₁ , e₂) , (f₁ , f₂) , (g₁ , g₂) , (h₁ , h₂)) F
    Preserving₇ = Preserving 7

    Preserving₈ : PreservingSignature 8 ((a₁ , a₂) , (b₁ , b₂) , (c₁ , c₂) , (d₁ , d₂) , (e₁ , e₂) , (f₁ , f₂) , (g₁ , g₂) , (h₁ , h₂) , (i₁ , i₂)) F
    Preserving₈ = Preserving 8

    Preserving₉ : PreservingSignature 9 ((a₁ , a₂) , (b₁ , b₂) , (c₁ , c₂) , (d₁ , d₂) , (e₁ , e₂) , (f₁ , f₂) , (g₁ , g₂) , (h₁ , h₂) , (i₁ , i₂) , (j₁ , j₂)) F
    Preserving₉ = Preserving 9

  Preserving = \x {S} {F} → Indexed.Preserving(Tuple.uncurry(_⟶₁_)) (Tuple.uncurry(_⟶₂_)) ⦃ morphism-equiv₂ ⦄ x {S} {Tuple.map F F}
  preserving = \x {S} {F} → Indexed.preserving(Tuple.uncurry(_⟶₁_)) (Tuple.uncurry(_⟶₂_)) ⦃ morphism-equiv₂ ⦄ x {S} {Tuple.map F F}
  module Preserving = Indexed.Preserving {A = Tuple.uncurry(_⟶₁_)} {B = Tuple.uncurry(_⟶₂_)} ⦃ morphism-equiv₂ ⦄
  open Indexed using (intro) public

  Preserving₀ : Names.PreservingSignature 0 (a₁ , a₂) F
  Preserving₀ = Preserving 0
  preserving₀ = preserving 0

  Preserving₁ : Names.PreservingSignature 1 ((a₁ , a₂) , (b₁ , b₂)) F
  Preserving₁ = Preserving 1
  preserving₁ = preserving 1

  Preserving₂ : Names.PreservingSignature 2 ((a₁ , a₂) , (b₁ , b₂) , (c₁ , c₂)) F
  Preserving₂ = Preserving 2
  preserving₂ = preserving 2

  Preserving₃ : Names.PreservingSignature 3 ((a₁ , a₂) , (b₁ , b₂) , (c₁ , c₂) , (d₁ , d₂)) F
  Preserving₃ = Preserving 3
  preserving₃ = preserving 3

  Preserving₄ : Names.PreservingSignature 4 ((a₁ , a₂) , (b₁ , b₂) , (c₁ , c₂) , (d₁ , d₂) , (e₁ , e₂)) F
  Preserving₄ = Preserving 4
  preserving₄ = preserving 4

  Preserving₅ : Names.PreservingSignature 5 ((a₁ , a₂) , (b₁ , b₂) , (c₁ , c₂) , (d₁ , d₂) , (e₁ , e₂) , (f₁ , f₂)) F
  Preserving₅ = Preserving 5
  preserving₅ = preserving 5

  Preserving₆ : Names.PreservingSignature 6 ((a₁ , a₂) , (b₁ , b₂) , (c₁ , c₂) , (d₁ , d₂) , (e₁ , e₂) , (f₁ , f₂) , (g₁ , g₂)) F
  Preserving₆ = Preserving 6
  preserving₆ = preserving 6

  Preserving₇ : Names.PreservingSignature 7 ((a₁ , a₂) , (b₁ , b₂) , (c₁ , c₂) , (d₁ , d₂) , (e₁ , e₂) , (f₁ , f₂) , (g₁ , g₂) , (h₁ , h₂)) F
  Preserving₇ = Preserving 7
  preserving₇ = preserving 7

  Preserving₈ : Names.PreservingSignature 8 ((a₁ , a₂) , (b₁ , b₂) , (c₁ , c₂) , (d₁ , d₂) , (e₁ , e₂) , (f₁ , f₂) , (g₁ , g₂) , (h₁ , h₂) , (i₁ , i₂)) F
  Preserving₈ = Preserving 8
  preserving₈ = preserving 8

  Preserving₉ : Names.PreservingSignature 9 ((a₁ , a₂) , (b₁ , b₂) , (c₁ , c₂) , (d₁ , d₂) , (e₁ , e₂) , (f₁ , f₂) , (g₁ , g₂) , (h₁ , h₂) , (i₁ , i₂) , (j₁ , j₂)) F
  Preserving₉ = Preserving 9
  preserving₉ = preserving 9

{-
module Structure.Categorical.Functor.Properties where

open import Data
open import Data.Boolean
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Data.Tuple.Raiseᵣ using (_^_)
open import Functional using (_→ᶠ_ ; _on₂_)
open import Functional.Instance using (inferArg)
import      Lvl
open import Logic
open import Numeral.Natural
open import Numeral.Natural.Oper.Comparisons
open import Structure.Categorical.Functor
open import Structure.Setoid
open import Type

private variable ℓ ℓₒ ℓₘ ℓₘ₁ ℓₘ₂ ℓₑ ℓₑ₁ ℓₑ₂ : Lvl.Level
private variable Obj Obj₁ Obj₂ : Type{ℓₒ}
private variable a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ e₁ e₂ f₁ f₂ g₁ g₂ h₁ h₂ i₁ i₂ j₁ j₂ : Obj

open import Structure.IndexedOperator
import      Structure.IndexedOperator.Properties.Preserving as Indexed

module _
  (_⟶₁_ : Obj₁ → Obj₁ → Stmt{ℓₘ₁})
  ⦃ morphism-equiv₁ : ∀{x y} → Equiv{ℓₑ₁}(x ⟶₁ y) ⦄
  (_⟶₂_ : Obj₂ → Obj₂ → Stmt{ℓₘ₂})
  ⦃ morphism-equiv₂ : ∀{x y} → Equiv{ℓₑ₂}(x ⟶₂ y) ⦄
  where

  module Names where
    PreservingSignature = \n S → ∀{F : Obj₁ → Obj₂} → (∀{x y} → (x ⟶₁ y) → (F(x) ⟶₂ F(y))) → Operator(_⟶₁_)(𝐒(n)) S → Operator((_⟶₂_) on₂ F)(𝐒(n)) S → Stmt{if(positive?(n)) then (ℓₘ₁ Lvl.⊔ ℓₑ₂) else ℓₑ₂}

    -- A relation between a functor and two n-ary operations between morphisms that states:
    -- The functor preserves the operations.
    -- Often used when defining homomorphisms.
    -- Examples:
    --   Preserving(0) {x , y} (map)(G₁)(G₂)
    --   = (map ∘₀ G₁ ≡ G₂ on₀ map)
    --   = (map(G₁) ≡ G₂(f))
    --   Preserving(1) {(x , y) , (x , y)} (map)(G₁)(G₂)
    --   = ∀{f : x ⟶ y} → ((map ∘₁ G₁)(f) ≡ (G₂ on₁ map)(f))
    --   = ∀{f : x ⟶ y} → (map(G₁(f)) ≡ G₂(map(f)))
    --   Preserving(2) {(y , z) , (x , y) , (x , z)} (map)(G₁)(G₂)
    --   = ∀{f₁ : y ⟶ z}{f₂ : x ⟶ y} → ((map ∘₂ G₁)(f₁)(f₂) ≡ (G₂ on₂ map)(f₁)(f₂))
    --   = ∀{f₁ : y ⟶ z}{f₂ : x ⟶ y} → (map(G₁ f₁ f₂) ≡ G₂ (map(f₁)) (map(f₂)))
    --   Preserving(3) {(z , w) , (y , z) , (x , y) , (x , w)} (map)(G₁)(G₂)
    --   = ∀{f₁ f₂ f₃} → ((map ∘₃ G₁)(f₁)(f₂)(f₃) ≡ (G₂ on₃ map)(f₁)(f₂)(f₃))
    --   = ∀{f₁ f₂ f₃} → (map(G₁ f₁ f₂ f₃) ≡ G₂ (map(f₁)) (map(f₂)) (map(f₃)))
    Preserving : (n : ℕ) → {S : OperatorSignature(_⟶₁_)(𝐒(n))} → PreservingSignature n S
    Preserving 0        {x , y}       map G₁ G₂ = map(G₁) ≡ G₂
    Preserving 1        {(x , y) , o} map G₁ G₂ = ∀{f : x ⟶₁ y} → (map(G₁ f) ≡ G₂(map f))
    Preserving(𝐒(𝐒(n))) {(x , y) , o} map G₁ G₂ = ∀{f : x ⟶₁ y} → Preserving(𝐒(n)) {o} map (G₁ f) (G₂(map f))

    Preserving₀ : PreservingSignature 0 (a₁ , a₂)
    Preserving₀ = Preserving 0

    Preserving₁ : PreservingSignature 1 ((a₁ , a₂) , (b₁ , b₂))
    Preserving₁ = Preserving 1

    Preserving₂ : PreservingSignature 2 ((a₁ , a₂) , (b₁ , b₂) , (c₁ , c₂))
    Preserving₂ = Preserving 2

    Preserving₃ : PreservingSignature 3 ((a₁ , a₂) , (b₁ , b₂) , (c₁ , c₂) , (d₁ , d₂))
    Preserving₃ = Preserving 3

    Preserving₄ : PreservingSignature 4 ((a₁ , a₂) , (b₁ , b₂) , (c₁ , c₂) , (d₁ , d₂) , (e₁ , e₂))
    Preserving₄ = Preserving 4

    Preserving₅ : PreservingSignature 5 ((a₁ , a₂) , (b₁ , b₂) , (c₁ , c₂) , (d₁ , d₂) , (e₁ , e₂) , (f₁ , f₂))
    Preserving₅ = Preserving 5

    Preserving₆ : PreservingSignature 6 ((a₁ , a₂) , (b₁ , b₂) , (c₁ , c₂) , (d₁ , d₂) , (e₁ , e₂) , (f₁ , f₂) , (g₁ , g₂))
    Preserving₆ = Preserving 6

    Preserving₇ : PreservingSignature 7 ((a₁ , a₂) , (b₁ , b₂) , (c₁ , c₂) , (d₁ , d₂) , (e₁ , e₂) , (f₁ , f₂) , (g₁ , g₂) , (h₁ , h₂))
    Preserving₇ = Preserving 7

    Preserving₈ : PreservingSignature 8 ((a₁ , a₂) , (b₁ , b₂) , (c₁ , c₂) , (d₁ , d₂) , (e₁ , e₂) , (f₁ , f₂) , (g₁ , g₂) , (h₁ , h₂) , (i₁ , i₂))
    Preserving₈ = Preserving 8

    Preserving₉ : PreservingSignature 9 ((a₁ , a₂) , (b₁ , b₂) , (c₁ , c₂) , (d₁ , d₂) , (e₁ , e₂) , (f₁ , f₂) , (g₁ , g₂) , (h₁ , h₂) , (i₁ , i₂) , (j₁ , j₂))
    Preserving₉ = Preserving 9

  module _ (n : ℕ) {S : OperatorSignature(_⟶₁_)(𝐒(n))} {F : Obj₁ → Obj₂} (map : ∀{x y} → (x ⟶₁ y) → (F(x) ⟶₂ F(y))) (G₁ : Operator(_⟶₁_)(𝐒(n)) S) (G₂ : Operator((_⟶₂_) on₂ F)(𝐒(n)) S) where
    record Preserving : Stmt{if(positive?(n)) then (ℓₘ₁ Lvl.⊔ ℓₑ₂) else ℓₑ₂} where
      constructor intro
      field proof : Names.Preserving(n) map G₁ G₂
    preserving = inferArg Preserving.proof

  Preserving₀ : Names.PreservingSignature 0 (a₁ , a₂)
  Preserving₀ = Preserving 0
  preserving₀ = preserving 0

  Preserving₁ : Names.PreservingSignature 1 ((a₁ , a₂) , (b₁ , b₂))
  Preserving₁ = Preserving 1
  preserving₁ = preserving 1

  Preserving₂ : Names.PreservingSignature 2 ((a₁ , a₂) , (b₁ , b₂) , (c₁ , c₂))
  Preserving₂ = Preserving 2
  preserving₂ = preserving 2

  Preserving₃ : Names.PreservingSignature 3 ((a₁ , a₂) , (b₁ , b₂) , (c₁ , c₂) , (d₁ , d₂))
  Preserving₃ = Preserving 3
  preserving₃ = preserving 3

  Preserving₄ : Names.PreservingSignature 4 ((a₁ , a₂) , (b₁ , b₂) , (c₁ , c₂) , (d₁ , d₂) , (e₁ , e₂))
  Preserving₄ = Preserving 4
  preserving₄ = preserving 4

  Preserving₅ : Names.PreservingSignature 5 ((a₁ , a₂) , (b₁ , b₂) , (c₁ , c₂) , (d₁ , d₂) , (e₁ , e₂) , (f₁ , f₂))
  Preserving₅ = Preserving 5
  preserving₅ = preserving 5

  Preserving₆ : Names.PreservingSignature 6 ((a₁ , a₂) , (b₁ , b₂) , (c₁ , c₂) , (d₁ , d₂) , (e₁ , e₂) , (f₁ , f₂) , (g₁ , g₂))
  Preserving₆ = Preserving 6
  preserving₆ = preserving 6

  Preserving₇ : Names.PreservingSignature 7 ((a₁ , a₂) , (b₁ , b₂) , (c₁ , c₂) , (d₁ , d₂) , (e₁ , e₂) , (f₁ , f₂) , (g₁ , g₂) , (h₁ , h₂))
  Preserving₇ = Preserving 7
  preserving₇ = preserving 7

  Preserving₈ : Names.PreservingSignature 8 ((a₁ , a₂) , (b₁ , b₂) , (c₁ , c₂) , (d₁ , d₂) , (e₁ , e₂) , (f₁ , f₂) , (g₁ , g₂) , (h₁ , h₂) , (i₁ , i₂))
  Preserving₈ = Preserving 8
  preserving₈ = preserving 8

  Preserving₉ : Names.PreservingSignature 9 ((a₁ , a₂) , (b₁ , b₂) , (c₁ , c₂) , (d₁ , d₂) , (e₁ , e₂) , (f₁ , f₂) , (g₁ , g₂) , (h₁ , h₂) , (i₁ , i₂) , (j₁ , j₂))
  Preserving₉ = Preserving 9
  preserving₉ = preserving 9
-}
