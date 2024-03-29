-- Example:
--   postulate ℓ : Lvl.Level
--   postulate A B C D : Type{ℓ}
--   postulate a : A
--   postulate ab : A → B
--   postulate bc : B → C
--   postulate cd : C → D
--
--   ad : A → D
--   ad =
--     A ⇒-[ ab ]
--     B ⇒-[ bc ]
--     C ⇒-[ cd ]
--     D ⇒-end
--
--   d : D
--   d =
--     a ⇒
--     A ⇒-[ ab ]
--     B ⇒-[ bc ]
--     C ⇒-[ cd ]
--     D ⇒-end
module Syntax.Implication where

open import Functional using (const ; id ; _∘_ ; _∘₂_ ; _∘₃_ ; swap)
open import Logic.Propositional
import      Lvl
import      Syntax.Implication.Dependent as Dependent
open import Type

private variable ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ : Lvl.Level

open Dependent using (_⇒-end ; _⇒_) public

_⇒-start_ : ∀{X : Type{ℓ₁}}{Y : Type{ℓ₂}} → X → (X → Y) → Y
_⇒-start_ x xy = xy x
infixr 0.98 _⇒-start_
{-# INLINE _⇒-start_ #-}

_⇒-[_]_ : ∀(X : Type{ℓ₁}){Y : Type{ℓ₂}}{Z : Type{ℓ₃}} → (X → Y) → (Y → Z) → (X → Z)
_⇒-[_]_ _ = swap(_∘_)
infixr 0.98 _⇒-[_]_
{-# INLINE _⇒-[_]_ #-}

_⇒-[]_ : ∀(X : Type{ℓ₁}){Y : Type{ℓ₂}} → (X → Y) → (X → Y)
_⇒-[]_ _ = id
infixr 0.98 _⇒-[]_
{-# INLINE _⇒-[]_ #-}

•_⇒₁_ : ∀{X : Type{ℓ₁}}{Y : Type{ℓ₂}} → X → (X → Y) → Y
•_⇒₁_ x f = f x
infixr 0.97 •_⇒₁_
{-# INLINE •_⇒₁_ #-}

•_•_⇒₂-[_]_ : ∀{X₁ : Type{ℓ₁}}{X₂ : Type{ℓ₂}}{Y : Type{ℓ₃}}{Z : Type{ℓ₄}} → X₁ → X₂ → (X₁ → X₂ → Y) → (Y → Z) → Z
•_•_⇒₂-[_]_ x₁ x₂ g f = (f ∘₂ g) x₁ x₂
infixr 0.97 •_•_⇒₂-[_]_
{-# INLINE •_•_⇒₂-[_]_ #-}

•_•_•_⇒₃-[_]_ : ∀{X₁ : Type{ℓ₁}}{X₂ : Type{ℓ₂}}{X₃ : Type{ℓ₃}}{Y : Type{ℓ₄}}{Z : Type{ℓ₅}} → X₁ → X₂ → X₃ → (X₁ → X₂ → X₃ → Y) → (Y → Z) → Z
•_•_•_⇒₃-[_]_ x₁ x₂ x₃ g f = (f ∘₃ g) x₁ x₂ x₃
infixr 0.97 •_•_•_⇒₃-[_]_
{-# INLINE •_•_•_⇒₃-[_]_ #-}

_⇔-end : ∀(X : Type{ℓ₁}) → (X ↔ X)
_⇔-end _ = [↔]-intro id id
infixr 0.99 _⇔-end
{-# INLINE _⇔-end #-}


_⇔_ : ∀{X : Type{ℓ₁}}{Y : Type{ℓ₂}}{Z : Type{ℓ₃}} → (X ↔ Y) → (Y ↔ Z) → (X ↔ Z)
_⇔_ ([↔]-intro pₗ pᵣ) ([↔]-intro qₗ qᵣ) = [↔]-intro (pₗ ∘ qₗ) (qᵣ ∘ pᵣ)
infixl 0.97 _⇔_
{-# INLINE _⇔_ #-}

_⇔-sym_ : ∀{X : Type{ℓ₁}}{Y : Type{ℓ₂}}{Z : Type{ℓ₃}} → (X ↔ Y) → (Z ↔ Y) → (X ↔ Z)
_⇔-sym_ ([↔]-intro pₗ pᵣ) ([↔]-intro qₗ qᵣ) = [↔]-intro (pₗ ∘ qᵣ) (qₗ ∘ pᵣ)
infixl 0.97 _⇔-sym_
{-# INLINE _⇔-sym_ #-}

_⇔-[_]_ : ∀(X : Type{ℓ₁}){Y : Type{ℓ₂}}{Z : Type{ℓ₃}} → (X ↔ Y) → (Y ↔ Z) → (X ↔ Z)
_⇔-[_]_ _ ([↔]-intro pₗ pᵣ) ([↔]-intro qₗ qᵣ) = [↔]-intro (pₗ ∘ qₗ) (qᵣ ∘ pᵣ)
infixr 0.98 _⇔-[_]_
{-# INLINE _⇔-[_]_ #-}

_⇔-[_]-sym_ : ∀(X : Type{ℓ₁}){Y : Type{ℓ₂}}{Z : Type{ℓ₃}} → (Y ↔ X) → (Y ↔ Z) → (X ↔ Z)
_⇔-[_]-sym_ X ([↔]-intro pₗ pᵣ) q = X ⇔-[ ([↔]-intro pᵣ pₗ) ] q
infixr 0.98 _⇔-[_]-sym_
{-# INLINE _⇔-[_]-sym_ #-}

_⇔-[]_ : ∀(X : Type{ℓ₁}){Y : Type{ℓ₂}} → (X ↔ Y) → (X ↔ Y)
_⇔-[]_ _ = id
infixr 0.98 _⇔-[]_
{-# INLINE _⇔-[]_ #-}
