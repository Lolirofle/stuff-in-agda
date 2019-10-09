module Type.Dependent.Functions where

import      Lvl
open import Functional
open import Type
open import Type.Dependent

module _ {ℓ₁ ℓ₂ ℓ₃}
         {A : Type{ℓ₁}}
         {B : A → Type{ℓ₂}}
         {C : ∀{x} → B(x) → Type{ℓ₃}}
         (f : ∀{x} → Π(B(x))(C))
         (g : Π(A)(B))
         where
  [Π]-∘ : Π(A)(\x → C(Π.apply g x))
  Π.apply [Π]-∘ x = Π.apply f (Π.apply g x)

module _ {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
         {A₁ : Type{ℓ₁}}
         {B₁ : A₁ → Type{ℓ₂}}
         {A₂ : Type{ℓ₃}}
         {B₂ : A₂ → Type{ℓ₄}}
         where
  [Σ]-map : (x : Σ(A₁)(B₁)) → (l : A₁ → A₂) → (r : B₁(Σ.left x) → B₂(l(Σ.left x))) → Σ(A₂)(B₂)
  [Σ]-map x l r = intro(l(Σ.left x))(r(Σ.right x))

module _ {ℓ₁ ℓ₂ ℓ₃}
         {A : Type{ℓ₁}}
         {B₁ : A → Type{ℓ₂}}
         {B₂ : A → Type{ℓ₃}}
         where
  [Σ]-mapᵣ : (x : Σ(A)(B₁)) → (r : B₁(Σ.left x) → B₂(Σ.left x)) → Σ(A)(B₂)
  [Σ]-mapᵣ x r = intro(Σ.left x)(r(Σ.right x))
