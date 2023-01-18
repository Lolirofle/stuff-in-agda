module Miscellaneous.FreeGroup where

open import Data.Either as Either using (_‖_ ; Left ; Right)
open import Data.List using (List ; ∅ ; _⊰_ ; _⊱_)
open import Data.List.Functions as List
open import Functional as Fn
import      Lvl
open import Structure.Relator.Names
open import Type

private variable ℓ : Lvl.Level
private variable T : Type{ℓ}

InvList : Type{ℓ} → Type
InvList(T) = List(T ‖ T)

inv : InvList(T) → InvList(T)
inv = foldₗ(Fn.swap((_⊰_) ∘ Either.swap)) ∅

module _ (let _ = T) where
  data _≡ᵍʳᵒᵘᵖ_ : InvList(T) → InvList(T) → Type{Lvl.of(T)} where
    empty          : ∅ ≡ᵍʳᵒᵘᵖ ∅
    prepend        : ∀{x}{l₁ l₂} → (l₁ ≡ᵍʳᵒᵘᵖ l₂) → (x ⊰ l₁ ≡ᵍʳᵒᵘᵖ x ⊰ l₂)
    left-inverseₗ  : ∀{x}{l₁ l₂} → (l₁ ≡ᵍʳᵒᵘᵖ l₂) → (Left x ⊰ Right x ⊰ l₁ ≡ᵍʳᵒᵘᵖ l₂)
    left-inverseᵣ  : ∀{x}{l₁ l₂} → (l₁ ≡ᵍʳᵒᵘᵖ l₂) → (Right x ⊰ Left x ⊰ l₁ ≡ᵍʳᵒᵘᵖ l₂)
    right-inverseₗ : ∀{x}{l₁ l₂} → (l₁ ≡ᵍʳᵒᵘᵖ l₂) → (l₁ ≡ᵍʳᵒᵘᵖ Left x ⊰ Right x ⊰ l₂)
    right-inverseᵣ : ∀{x}{l₁ l₂} → (l₁ ≡ᵍʳᵒᵘᵖ l₂) → (l₁ ≡ᵍʳᵒᵘᵖ Right x ⊰ Left x ⊰ l₂)

  module _
    (P : ∀{l₁ l₂} → (l₁ ≡ᵍʳᵒᵘᵖ l₂) → Type{ℓ})
    (pe  : P(empty))
    (pp  : ∀{x}{l₁ l₂}{p} → P(p) → P(prepend{x}{l₁}{l₂} p))
    (pll : ∀{x}{l₁ l₂}{p} → P(p) → P(left-inverseₗ{x}{l₁}{l₂} p))
    (plr : ∀{x}{l₁ l₂}{p} → P(p) → P(left-inverseᵣ{x}{l₁}{l₂} p))
    (prl : ∀{x}{l₁ l₂}{p} → P(p) → P(right-inverseₗ{x}{l₁}{l₂} p))
    (prr : ∀{x}{l₁ l₂}{p} → P(p) → P(right-inverseᵣ{x}{l₁}{l₂} p))
    where

    elim : ∀{l₁ l₂}(p) → P{l₁}{l₂}(p)
    elim empty              = pe
    elim (prepend        p) = pp  (elim p)
    elim (left-inverseₗ  p) = pll (elim p)
    elim (left-inverseᵣ  p) = plr (elim p)
    elim (right-inverseₗ p) = prl (elim p)
    elim (right-inverseᵣ p) = prr (elim p)

  refl : Reflexivity(_≡ᵍʳᵒᵘᵖ_)
  refl{∅}     = empty
  refl{x ⊰ l} = prepend(refl{l})

  sym : Symmetry(_≡ᵍʳᵒᵘᵖ_)
  sym empty              = empty
  sym (prepend p)        = prepend (sym p)
  sym (left-inverseₗ p)  = right-inverseₗ (sym p)
  sym (left-inverseᵣ p)  = right-inverseᵣ (sym p)
  sym (right-inverseₗ p) = left-inverseₗ (sym p)
  sym (right-inverseᵣ p) = left-inverseᵣ (sym p)

  {-
  trans : Transitivity(_≡ᵍʳᵒᵘᵖ_)
  trans {∅} {∅} {∅} p q = q
  trans {∅} {∅} {prepend x z} p q = q
  trans {∅} {prepend x y} {∅} p q = empty
  trans {∅} {prepend x y} {prepend x₁ z} p q = {!!}
  trans {prepend x x₁} {∅} {∅} p q = p
  trans {prepend x x₁} {∅} {prepend x₂ z} p q = {!!}
  trans {prepend x x₁} {prepend x₂ y} {∅} p q = {!!}
  trans {prepend x x₁} {prepend x₂ y} {prepend x₃ z} p q = {!!}
  -}

  trans : Transitivity(_≡ᵍʳᵒᵘᵖ_)
  trans p q = elim(\{x}{y} p → ∀{z} → y ≡ᵍʳᵒᵘᵖ z → x ≡ᵍʳᵒᵘᵖ z)
    id
    (\p q → {!!})
    (left-inverseₗ ∘_)
    (left-inverseᵣ ∘_)
    {!!}
    {!!}
    p
    q

  trans' : Transitivity(_≡ᵍʳᵒᵘᵖ_)
  trans' empty q = q
  trans' {_ ⊰ _} {.(_ ⊰ _)} {∅} (prepend p) q = {!q!}
  trans' {_ ⊰ _} {.(_ ⊰ _)} {x ⊰ z} (prepend p) q = {!!}
  trans' (left-inverseₗ p) q = left-inverseₗ (trans' p q)
  trans' (left-inverseᵣ p) q = left-inverseᵣ (trans' p q)
  trans' (right-inverseₗ p) q = {!!}
  trans' (right-inverseᵣ p) q = {!!}
