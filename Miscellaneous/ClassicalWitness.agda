{-# OPTIONS --prop #-}

module Miscellaneous.ClassicalWitness where

open import Agda.Primitive using (Prop)

open import Data
open import Data.Either
open import Functional
import      Lvl
open import Type.Dependent.Sigma
open import Type

private variable ℓ ℓ₁ ℓ₂ : Lvl.Level
private variable T A B Obj : Type{ℓ}
private variable P Q R : Prop(ℓ)
private variable Pred : T → Prop(ℓ)
private variable x y z : T

empty-prop : Empty{ℓ} → P
empty-prop ()

data Proof(P : Prop(ℓ)) : Type{ℓ} where
  intro : P → Proof(P)

data ⊥ : Prop(Lvl.𝟎) where

[⊥]-elim : ⊥ → P
[⊥]-elim ()

[⊥]-elim-type : ⊥ → T
[⊥]-elim-type ()

¬_ : Prop(ℓ) → Prop(ℓ)
¬ P = P → ⊥

data _∧_ (P : Prop(ℓ₁)) (Q : Prop(ℓ₂)) : Prop(ℓ₁ Lvl.⊔ ℓ₂) where
  [∧]-intro : P → Q → (P ∧ Q)

data _∨_ (P : Prop(ℓ₁)) (Q : Prop(ℓ₂)) : Prop(ℓ₁ Lvl.⊔ ℓ₂) where
  [∨]-introₗ : P → (P ∨ Q)
  [∨]-introᵣ : Q → (P ∨ Q)

[∨]-elim : (P → R) → (Q → R) → (P ∨ Q) → R
[∨]-elim pr qr ([∨]-introₗ p) = pr p
[∨]-elim pr qr ([∨]-introᵣ q) = qr q

data ∃ {Obj : Type{ℓ₁}} (P : Obj → Prop(ℓ₂)) : Prop(ℓ₁ Lvl.⊔ ℓ₂) where
  [∃]-intro : (witness : Obj) → ⦃ proof : P(witness) ⦄ → ∃(P)

[∃]-elim : (∀{x} → Pred(x) → P) → (∃ Pred) → P
[∃]-elim pr ([∃]-intro _ ⦃ p ⦄) = pr p

∃-empty-type : (∀{x : Obj} → Pred(x) → Empty{ℓ}) → ¬(∃{Obj = Obj} Pred)
∃-empty-type empty-p ep = [∃]-elim (\px → empty-prop (empty-p px)) ep

data Inhabited(T : Type{ℓ}) : Prop(Lvl.𝐒(ℓ)) where
  intro : T → Inhabited(T)

Inhabited-elim : (T → P) → (Inhabited(T) → P)
Inhabited-elim f (intro obj) = f(obj)

Inhabited-empty-type : (T → Empty{ℓ}) → (¬ Inhabited(T))
Inhabited-empty-type empty-T inhab-T = Inhabited-elim (\t → empty-prop(empty-T t)) inhab-T

∃-to-Inhabited : (∃{Obj = Obj} Pred) → Inhabited(Obj)
∃-to-Inhabited = [∃]-elim (\{x} _ → intro x)

data _≡_ {T : Type{ℓ}} : T → T → Prop(Lvl.of(T)) where
  refl : ∀{x} → (x ≡ x)

sym : ∀{x y : T} → (x ≡ y) → (y ≡ x)
sym refl = refl

subst : (P : T → Prop(ℓ)) → ∀{x y : T} → (x ≡ y) → (P(x) → P(y))
subst P refl = (\x → x)

data Singleton(T : Type{ℓ}) : Prop(Lvl.𝐒(ℓ)) where
  intro : (x : T) → (∀{y} → (x ≡ y)) → Singleton(T)

data ∃! {Obj : Type{ℓ₁}} (P : Obj → Prop(ℓ₂)) : Prop(ℓ₁ Lvl.⊔ ℓ₂) where
  [∃!]-intro : (witness : Obj) → ⦃ proof : P(witness) ⦄ → (∀{x} → P(x) → (witness ≡ x)) → ∃!(P)

[∃!]-elim : (∀{x} → Pred(x) → (∀{y} → (Pred(y)) → (x ≡ y)) → P) → (∃! Pred) → P
[∃!]-elim pr ([∃!]-intro _ ⦃ p ⦄ eq) = pr p eq

∃!-to-∃ : (∃!{Obj = Obj} Pred) → (∃{Obj = Obj} Pred)
∃!-to-∃ = [∃!]-elim (\{x} p _ → [∃]-intro x ⦃ p ⦄)

∃!-empty-type : (∀{x : Obj} → Pred(x) → Empty{ℓ}) → ¬(∃!{Obj = Obj} Pred)
∃!-empty-type empty-p ep = [∃!]-elim (\px → empty-prop (empty-p px)) ep

module WhenExcludedMiddle (excluded-middle : ∀{ℓ}(P : Prop(ℓ)) → (P ∨ (¬ P))) where
  {-[¬¬]-elim-type : ((T → ⊥) → ⊥) → T
  [¬¬]-elim-type {T = T} nnt with excluded-middle(T)
  ... | p = ?-}

  {-
  decidable : ∀{ℓ ℓₑ}(T : Type{ℓ}) → (T ‖ (T → Empty{ℓₑ}))
  decidable(T) = {!excluded-middle!}
  -}

  {-
  singleton-witness : Singleton(T) → T
  singleton-witness x = {!!}
  -}

module WhenDNEType ([¬¬]-elim-type : ∀{ℓ}{T : Type{ℓ}} → ((T → ⊥) → ⊥) → T) where
  inhabited-witness : Inhabited(T) → T
  inhabited-witness p = [¬¬]-elim-type (\nt → Inhabited-elim nt p)

module WhenDecidable {ℓₑ} (decidable : ∀{ℓ}(T : Type{ℓ}) → (T ‖ (T → Empty{ℓₑ}))) where
  excluded-middle : ∀{ℓ}(P : Prop(ℓ)) → (P ∨ (¬ P))
  excluded-middle(P) with decidable(Proof P)
  ... | Left (intro p) = [∨]-introₗ p
  ... | Right np       = [∨]-introᵣ (\p → empty-prop(np(intro p)))

  inhabited-witness : Inhabited(T) → T -- TODO: Are there any other ways (with weaker assumptions) of doing this?
  inhabited-witness{T = T} x with decidable(T)
  ... | Left  t  = t
  ... | Right nt = [⊥]-elim-type (Inhabited-empty-type nt x)

  ∃-to-Σ : (∃{Obj = Obj} Pred) → (Σ Obj (\p → Proof(Pred p)))
  ∃-to-Σ {Obj = Obj}{Pred = Pred} ep with decidable(Σ Obj (\p → Proof(Pred p)))
  ... | Left  s  = s
  ... | Right ns = [⊥]-elim-type (∃-empty-type (\{x} px → ns (intro x (intro px))) ep)

  [∃]-witness : (∃{Obj = Obj} Pred) → Obj
  [∃]-witness {Obj = Obj}{Pred = Pred} ep = Σ.left (∃-to-Σ ep)
  -- inhabited-witness(∃-to-Inhabited(∃!-to-∃ ep))

  [∃]-proof : (ep : ∃{Obj = Obj} Pred) → Pred([∃]-witness ep)
  [∃]-proof {Obj = Obj}{Pred = Pred} ep with intro p ← Σ.right (∃-to-Σ ep) = p
  -- [∃!]-elim (\p eq → subst(Pred) {!eq p!} p) ep

module WhenInhabitedWitness (inhabited-witness : ∀{ℓ}{T : Type{ℓ}} → Inhabited(T) → T) where
  [∨]-elim-type : (P → T) → (Q → T) → (P ∨ Q) → T
  [∨]-elim-type pt qt pq = inhabited-witness([∨]-elim (\t → intro(pt t)) (\t → intro(qt t)) pq)

  {-
  [∃]-witness : ∀{P : T → Prop(ℓ)} → (∃ P) → T -- TODO: Not really the witness. See TODO in [∃]-proof below
  [∃]-witness ep = inhabited-witness(∃-to-Inhabited ep)

  [∃]-proof : ∀{P : T → Prop(ℓ)} → (ep : ∃ P) → P([∃]-witness ep) -- TODO: Will not work because the witness obtained from `inhabited-witness` (this one is from `decidable`) can obviously be different from the one provided to prove (∃ P) (this one is from `[∃]-intro`). Though, a correct witness _is_ obtainable from (∃! P) as usual in classical logic.
  [∃]-proof{T = T} ep with decidable(T)
  ... | Left  t  = {!!}
  ... | Right nt = {!!}
  -}
