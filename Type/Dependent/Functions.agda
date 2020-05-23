module Type.Dependent.Functions where

import      Lvl
open import Functional.Dependent
open import Type
open import Type.Dependent
open import Syntax.Function

module _ {ℓ₁ ℓ₂ ℓ₃}
         {A : Type{ℓ₁}}
         {B : A → Type{ℓ₂}}
         {C : ∀{x} → B(x) → Type{ℓ₃}}
         where
  _[Π]-∘_ : (∀{x} → Π(B(x))(C)) → (g : Π(A)(B)) → Π(A)(\x → C(Π.apply g x))
  Π.apply (f [Π]-∘ g) x = Π.apply f (Π.apply g x)

  depCurry : (Π(Σ A B) (C ∘ Σ.right)) → (Π A (a ↦ (Π(B(a)) C)))
  Π.apply (Π.apply (depCurry f) a) b = Π.apply f (intro a b)

  depUncurry : (Π A (a ↦ Π(B(a)) C)) → (Π(Σ A B) (C ∘ Σ.right))
  Π.apply (depUncurry f) (intro a b) = Π.apply(Π.apply f a) b

module _ {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
         {A₁ : Type{ℓ₁}}
         {B₁ : A₁ → Type{ℓ₂}}
         {A₂ : Type{ℓ₃}}
         {B₂ : A₂ → Type{ℓ₄}}
         where
  [Σ]-apply : (x : Σ(A₁)(B₁)) → (l : A₁ → A₂) → (r : B₁(Σ.left x) → B₂(l(Σ.left x))) → Σ(A₂)(B₂)
  [Σ]-apply x l r = intro(l(Σ.left x))(r(Σ.right x))

  [ℰ]-apply : (x : Σ(A₁)(B₁)) → {l : A₁ → A₂} → (r : B₁(Σ.left x) → B₂(l(Σ.left x))) → Σ(A₂)(B₂)
  [ℰ]-apply x {l} r = [Σ]-apply x l r

  [Σ]-map : (l : A₁ → A₂) → (∀{a} → B₁(a) → B₂(l(a))) → (Σ(A₁)(B₁) → Σ(A₂)(B₂))
  [Σ]-map l r (intro left right) = intro (l left) (r right)

  [ℰ]-map : ∀{l : A₁ → A₂} → (∀{a} → B₁(a) → B₂(l(a))) → (Σ(A₁)(B₁) → Σ(A₂)(B₂))
  [ℰ]-map {l} = [Σ]-map l

module _ {ℓ₁ ℓ₂ ℓ₃}
         {A : Type{ℓ₁}}
         {B₁ : A → Type{ℓ₂}}
         {B₂ : A → Type{ℓ₃}}
         where
  [Σ]-applyᵣ : (x : Σ(A)(B₁)) → (r : B₁(Σ.left x) → B₂(Σ.left x)) → Σ(A)(B₂)
  [Σ]-applyᵣ x r = intro(Σ.left x)(r(Σ.right x))

module _ {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆}
         {A₁ : Type{ℓ₁}}
         {B₁ : A₁ → Type{ℓ₂}}
         {A₂ : Type{ℓ₃}}
         {B₂ : A₂ → Type{ℓ₄}}
         {A₃ : Type{ℓ₅}}
         {B₃ : A₃ → Type{ℓ₆}}
         where
  [Σ]-apply₂ : (x : Σ(A₁)(B₁)) → (y : Σ(A₂)(B₂)) → (l : A₁ → A₂ → A₃) → (r : B₁(Σ.left x) → B₂(Σ.left y) → B₃(l(Σ.left x)(Σ.left y))) → Σ(A₃)(B₃)
  [Σ]-apply₂ x y l r = intro(l(Σ.left x)(Σ.left y))(r(Σ.right x)(Σ.right y))

  [ℰ]-apply₂ : (x : Σ(A₁)(B₁)) → (y : Σ(A₂)(B₂)) → {l : A₁ → A₂ → A₃} → (r : B₁(Σ.left x) → B₂(Σ.left y) → B₃(l(Σ.left x)(Σ.left y))) → Σ(A₃)(B₃)
  [ℰ]-apply₂ x y {l} r = [Σ]-apply₂ x y l r

  [Σ]-map₂ : (l : A₁ → A₂ → A₃) → (∀{a₁}{a₂} → B₁(a₁) → B₂(a₂) → B₃(l a₁ a₂)) → (Σ(A₁)(B₁) → Σ(A₂)(B₂) → Σ(A₃)(B₃))
  [Σ]-map₂ l r (intro left₁ right₁) (intro left₂ right₂) = intro (l left₁ left₂) (r right₁ right₂)

  [ℰ]-map₂ : ∀{l : A₁ → A₂ → A₃} → (∀{a₁}{a₂} → B₁(a₁) → B₂(a₂) → B₃(l a₁ a₂)) → (Σ(A₁)(B₁) → Σ(A₂)(B₂) → Σ(A₃)(B₃))
  [ℰ]-map₂ {l} = [Σ]-map₂ l
