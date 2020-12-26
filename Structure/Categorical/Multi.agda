module Structure.Categorical.Multi where

open import Data
open import Data.Boolean
open import Data.Tuple using (_⨯_ ; _,_)
open import Data.Tuple.Raiseᵣ
import      Data.Tuple.Raiseᵣ.Functions as Raise
open import Data.Tuple.RaiseTypeᵣ
import      Data.Tuple.RaiseTypeᵣ.Functions as RaiseType
open import Function.Multi
open import Function.Multi.Functions
open import Functional using (_→ᶠ_)
import      Functional.Dependent as Fn
open import Lang.Instance
import      Lvl
open import Logic
open import Logic.Predicate
open import Logic.Propositional
open import Numeral.Natural
open import Numeral.Natural.Oper.Comparisons
open import Structure.Setoid
import      Structure.Categorical.Names as Names
import      Structure.Operator.Names as Names
import      Structure.Relator.Names as Names
open import Structure.Relator.Properties
open import Syntax.Function
open import Type
open import Type.Properties.Singleton

private variable ℓ ℓₒ ℓₘ ℓₘ₁ ℓₘ₂ ℓₑ ℓₑ₁ ℓₑ₂ : Lvl.Level
private variable Obj Obj₁ Obj₂ : Type{ℓₒ}

module Morphism where
  module _
    (_⟶_ : Obj → Obj → Stmt{ℓₘ})
    ⦃ morphism-equiv : ∀{x y} → Equiv{ℓₑ}(x ⟶ y) ⦄
    where

    {-
    -- Examples:
    --   MorphismChain(3) T x y z
    --   = compose(1) ((x ⟶ y) ,_) (MorphismChain(2) T y) z
    --   = (x ⟶ y) , (MorphismChain(2) T y z)
    --   = (x ⟶ y) , (y ⟶ z) , T(z)
    --
    --   MorphismChain(4) T x y z w
    --   = compose(2) ((x ⟶ y) ,_) (MorphismChain(3) T y) z w
    --   = (x ⟶ y) , (MorphismChain(3) T y z w)
    --   = (x ⟶ y) , (y ⟶ z) , (z ⟶ w) , T(w)
    MorphismChain : (n : ℕ) → (Obj → Type{ℓₘ}) → (RaiseType.repeat (𝐒(n)) Obj) ⇉ Types(Raise.repeat (𝐒(n)) ℓₘ)
    MorphismChain 0         T x   = T(x)
    MorphismChain 1         T x y = (x ⟶ y) , T(y)
    MorphismChain (𝐒(𝐒(n))) T x y = compose(𝐒(n)) ((x ⟶ y) ,_) (MorphismChain(𝐒(n)) T y)

    -- Examples:
    --   MorphismMapping(2) x y
    --   = MorphismChain(2)(x ⟶_) x y
    --   = (x ⟶ y) → (x ⟶ y)
    --
    --   MorphismMapping(3) x y z
    --   = MorphismChain(3)(x ⟶_) x y z
    --   = (x ⟶ y) → (y ⟶ z) → (x ⟶ z)
    --
    --   MorphismMapping(4) x y z w
    --   = MorphismChain(4)(x ⟶_) x y z w
    --   = (x ⟶ y) → (y ⟶ z) → (z ⟶ w) → (x ⟶ w)
    MorphismMapping : (n : ℕ) → (RaiseType.repeat n Obj) ⇉ Type{ℓₘ}
    MorphismMapping(0)   = Unit
    MorphismMapping(1)      = {!!}
    MorphismMapping(𝐒(𝐒 n)) = {!!}
    --MorphismMapping(𝐒 n) = curry(n) {!Fs ↦ (uncurry(n) (MorphismChain(n)) Fs ⇉ (? → ?))!}
    {-
    MorphismMapping(1)       x   = ? -- MorphismChain(1)(x ⟶_) x
    MorphismMapping(𝐒(𝐒(n))) x   = compose(𝐒(n)) (RaiseType.reduceᵣ{𝐒(n)}{\ℓ₁ ℓ₂ → ℓ₁ Lvl.⊔ ℓ₂} _→ᶠ_) (MorphismChain(𝐒(𝐒(n))) (x ⟶_) x)
    -- MorphismChain(𝐒(𝐒(n)))(x ⟶_) x-}
    -}

    MorphismFlippedChain : (n : ℕ) → (RaiseType.repeat (𝐒(n)) Obj) ⇉ Type{ℓₘ}
    MorphismFlippedChain 𝟎      x = x ⟶ x
    MorphismFlippedChain (𝐒(n)) x = Out(𝐒(n)) (x ⟶_) x where
      Out : (n : ℕ) → (Obj → Type{ℓₘ}) → (RaiseType.repeat (𝐒(n)) Obj) ⇉ Type{ℓₘ}
      Out 0         T x   = T(x)
      Out 1         T x y = (x ⟶ y) → T(y)
      Out (𝐒(𝐒(n))) T x y = Out(𝐒(n)) (z ↦ ((x ⟶ y) → T(z))) y

  module _ 
    (_⟶₁_ : Obj₁ → Obj₁ → Stmt{ℓₘ₁})
    ⦃ morphism-equiv₁ : ∀{x y} → Equiv{ℓₑ₁}(x ⟶₁ y) ⦄
    (_⟶₂_ : Obj₂ → Obj₂ → Stmt{ℓₘ₂})
    ⦃ morphism-equiv₂ : ∀{x y} → Equiv{ℓₑ₂}(x ⟶₂ y) ⦄
    where

    private open module Equiv₂{x}{y} = Equiv(morphism-equiv₂{x}{y}) using () renaming (_≡_ to _≡₂_)

    module _
      {F : Obj₁ → Obj₂}
      where

      -- Definition of the relation between a function and an operation that says:
      -- The function preserves the operation.
      -- Often used when defining homomorphisms.
      -- Examples:
      --   Preserving(0) (map)(G₁)(G₂)
      --   = ∀{x} → (map ∘₀ G₁ ≡ G₂ on₀ map)
      --   = ∀{x} → (map(G₁) ≡ G₂(f))
      --   Preserving(1) (map)(G₁)(G₂)
      --   = ∀{x y}{f : x ⟶ y} → ((map ∘₁ G₁)(f) ≡ (G₂ on₁ map)(f))
      --   = ∀{x y}{f : x ⟶ y} → (map(G₁(f)) ≡ G₂(map(f)))
      --   Preserving(2) (map)(G₁)(G₂)
      --   = ∀{x y z}{f₁ : y ⟶ z}{f₂ : x ⟶ y} → ((map ∘₂ G₁)(f₁)(f₂) ≡ (G₂ on₂ map)(f₁)(f₂))
      --   = ∀{x y z}{f₁ : y ⟶ z}{f₂ : x ⟶ y} → (map(G₁ f₁ f₂) ≡ G₂ (map(f₁)) (map(f₂)))
      --   Preserving(3) (map)(G₁)(G₂)
      --   = ∀{f₁ f₂ f₃} → ((map ∘₃ G₁)(f₁)(f₂)(f₃) ≡ (G₂ on₃ map)(f₁)(f₂)(f₃))
      --   = ∀{f₁ f₂ f₃} → (map(G₁ f₁ f₂ f₃) ≡ G₂ (map(f₁)) (map(f₂)) (map(f₃)))
      Preserving : (n : ℕ) → (map : ∀{x y} → (x ⟶₁ y) → (F(x) ⟶₂ F(y))) → (quantifier₊(𝐒(n))(∀ₗ) (MorphismFlippedChain(_⟶₁_)(n))) → (quantifier₊(𝐒(n))(∀ₗ) (MorphismFlippedChain(_⟶₂_)(n))) → (RaiseType.repeat (𝐒(n)) Obj₁) ⇉ Stmt{if(n ≤? 0) then (ℓₑ₂) else (ℓₘ₁ Lvl.⊔ ℓₑ₂)}
      Preserving 0            map G₁ G₂ x     = (map{x}(G₁) ≡ G₂)
      Preserving 1            map G₁ G₂ x y   = ∀{f : x ⟶₁ y} → map (G₁(f)) ≡ G₂(map f)
      Preserving (𝐒(𝐒(n)))    map G₁ G₂ x y   = {!Preserving(𝐒(n)) map ? ? y!}
      -- ∀{f} → (G₁(f)) (G₂(map f))
      --Preserving 2            map G₁ G₂ x y z = ∀{f₁ : y ⟶₁ z}{f₂ : x ⟶₁ y} → (map(G₁(f₁)(f₂)) ≡ G₂(map f₁)(map f₂))
      -- Preserving (𝐒(𝐒(𝐒(n)))) map G₁ G₂ x y z = {!∀{f} → Preserving(𝐒(𝐒(n))) map !}
      --test (P ↦ (∀{f} → P f)) (f ↦ Preserving (𝐒(𝐒(n))) map {!G₁!} {!G₂!} y z) where
      --  test : ((P : {!!}) → TYPE ({!!} Lvl.⊔ {!!})) → ((f : {!!} ⟶₁ {!!}) → RaiseType.repeat (𝐒 n) Obj₁ ⇉ Type) → (RaiseType.repeat (𝐒 n) Obj₁ ⇉ Type)
        -- compose(𝐒(n)) (P ↦ (∀{f} → P f)) ({!f ↦ Preserving (𝐒(𝐒(n))) map {!G₁!} {!G₂!} {!!} {!!}!})
      -- compose(𝐒(n)) {!!} {!!}
      -- ∀{f : x ⟶₁ y} → 
      -- Preserving(𝐒(𝐒(n))) map (\{a b} → {!G₁{a}{x}{b}!}) \{a b} → {!G₂{a}{F x}{b}!}

{-
-- Preserving 3 map G₁ G₂ a x y z
-- = ∀{f : a ⟶₁ x} → Preserving 2 map (G₁(f)) (G₂(map f)) x y z
-- = ∀{f : a ⟶₁ x}{f₁ : x ⟶₁ y}{f₂ : y ⟶₁ z} → (map(G₁(f)(f₁)(f₂)) ≡ G₂(map f)(map f₁)(map f₂))


      -- ∀{x y}{f : x ⟶₁ y} → Preserving(𝐒(𝐒(n))) (map) (G₁(f)) (G₂(map(f)))
{-      Preserving(𝟎)       (f)(g₁)(g₂) = (f(g₁) ≡ g₂)
      Preserving(𝐒(𝟎))    (f)(g₁)(g₂) = (∀{x} → f(g₁(x)) ≡ g₂(f(x)))
      Preserving(𝐒(𝐒(n))) (f)(g₁)(g₂) = (∀{x} → Preserving(𝐒(n)) (f) (g₁(x)) (g₂(f(x))))
  -- ∀{x y z : Objₗ}{f : y ⟶ z}{g : x ⟶ y} → (map(f ∘ g) ≡ map(f) ∘ map(g))
-}

-}
