module List.Properties where

import Level as Lvl
open import List
open import Relator.Equals(Lvl.𝟎)
open import Structure.Operator.Properties(Lvl.𝟎)

[++]-identityₗ : ∀{T} → Identityₗ {List T} (_++_) ∅
[++]-identityₗ = [≡]-intro

[++]-identityᵣ : ∀{T} → Identityᵣ {List T} (_++_) ∅
[++]-identityᵣ {T} = List-induction base next where
  base : (∅ ++ ∅) ≡ ∅
  base = [≡]-intro

  next : ∀(x : T)(l : List(T)) → ((l ++ ∅) ≡ l) → (((x ⤙ l) ++ ∅) ≡ (x ⤙ l))
  next x _ stmt = [≡]-with-[(λ list → x ⤙ list)] stmt
  -- (l ++ ∅) ≡ l
  -- x ⤙ (l ++ ∅) ≡ x ⤙ l
  -- (x ⤙ l) ++ ∅ ≡ x ⤙ l

[++]-associativity : ∀{T} → Associativity {List T} (_++_)
[++]-associativity {T} {l₀} {l₁} {l₂} = List-induction base next {l₀} where
  base : ((∅ ++ l₁) ++ l₂) ≡ (∅ ++ (l₁ ++ l₂))
  base = [≡]-intro
  -- l₁++l₂ = l₁++l₂
  -- ∅++(l₁++l₂) = (∅++l₁)++l₂

  next : ∀(x : T)(l : List(T)) → (((l ++ l₁) ++ l₂) ≡ (l ++ (l₁ ++ l₂))) → ((((x ⤙ l) ++ l₁) ++ l₂) ≡ ((x ⤙ l) ++ (l₁ ++ l₂)))
  next x _ stmt = [≡]-with-[(λ list → x ⤙ list)] stmt
  -- (l++l₁)++l₂ = l++(l₁++l₂)
  -- x ⤙ ((l++l₁)++l₂) = x ⤙ (l++(l₁++l₂))
  -- x ⤙ ((l++l₁)++l₂) = (x ⤙ l)++(l₁++l₂)
  -- (x ⤙ (l++l₁))++l₂ = (x ⤙ l)++(l₁++l₂)
  -- ((x ⤙ l)++l₁)++l₂ = (x ⤙ l)++(l₁++l₂)
