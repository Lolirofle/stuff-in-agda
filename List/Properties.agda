module List.Properties where

import Level as Lvl
open import List
open import Logic
open import Relator.Equals(Lvl.𝟎)
open import Structure.Operator.Properties(Lvl.𝟎)

[++]-identityₗ : ∀{T} → Identityₗ {List T} (_++_) ∅
[++]-identityₗ = [≡]-intro

[++]-identityᵣ : ∀{T} → Identityᵣ {List T} (_++_) ∅
[++]-identityᵣ {T} = List-induction base next where
  base : (∅ ++ ∅) ≡ ∅
  base = [≡]-intro

  next : ∀(x : T)(l : List(T)) → ((l ++ ∅) ≡ l) → (((x ⊰ l) ++ ∅) ≡ (x ⊰ l))
  next x _ stmt = [≡]-with-[(λ list → x ⊰ list)] stmt
  -- (l ++ ∅) ≡ l
  -- x ⊰ (l ++ ∅) ≡ x ⊰ l
  -- (x ⊰ l) ++ ∅ ≡ x ⊰ l

[++]-associativity : ∀{T} → Associativity {List T} (_++_)
[++]-associativity {T} {l₀} {l₁} {l₂} = List-induction base next {l₀} where
  base : ((∅ ++ l₁) ++ l₂) ≡ (∅ ++ (l₁ ++ l₂))
  base = [≡]-intro
  -- l₁++l₂ = l₁++l₂
  -- ∅++(l₁++l₂) = (∅++l₁)++l₂

  next : ∀(x : T)(l : List(T)) → (((l ++ l₁) ++ l₂) ≡ (l ++ (l₁ ++ l₂))) → ((((x ⊰ l) ++ l₁) ++ l₂) ≡ ((x ⊰ l) ++ (l₁ ++ l₂)))
  next x _ stmt = [≡]-with-[(λ list → x ⊰ list)] stmt
  -- (l++l₁)++l₂ = l++(l₁++l₂)
  -- x ⊰ ((l++l₁)++l₂) = x ⊰ (l++(l₁++l₂))
  -- x ⊰ ((l++l₁)++l₂) = (x ⊰ l)++(l₁++l₂)
  -- (x ⊰ (l++l₁))++l₂ = (x ⊰ l)++(l₁++l₂)
  -- ((x ⊰ l)++l₁)++l₂ = (x ⊰ l)++(l₁++l₂)

reverse-[++] : ∀{T}{l₁ l₂ : List(T)} → (reverse(l₁ ++ l₂) ≡ reverse(l₂) ++ reverse(l₁))
reverse-[++] {T} {l₁} {l₂} = List-induction base next {l₁} where
  base : reverse(∅ ++ l₂) ≡ reverse(l₂) ++ reverse(∅)
  base =
    ([≡]-transitivity([∧]-intro
      ([≡]-with-[ reverse ] {l₂} ([≡]-intro))
      ([≡]-symmetry [++]-identityᵣ)
    ))
  -- ∅++l = l //[++]-identityₗ
  -- reverse(∅++l) = l //[≡]-with-[ reverse ] (..)
  --   l = l++∅

  -- ([≡]-with-[ reverse ] {l₂} ([≡]-symmetry [++]-identityᵣ))
  -- l++∅ = l //[++]-identityᵣ
  -- l = l++∅ //[≡]-symmetry(..)
  -- reverse(l) = reverse(l++∅) //[≡]-with-[ reverse ] (..)
  -- ∅++reverse(l) = reverse(l++∅)
  -- reverse(∅)++reverse(l) = reverse(l++∅)

  next : ∀(x : T)(l : List(T)) → (reverse(l ++ l₂) ≡ reverse(l₂) ++ reverse(l)) → (reverse((x ⊰ l) ++ l₂) ≡ reverse(l₂) ++ reverse(x ⊰ l))
  next x l stmt =
    ([≡]-transitivity([∧]-intro
      ([≡]-with-[(λ list → list ++ (singleton x))] stmt)
      ([++]-associativity {_} {reverse(l₂)} {reverse(l)} {singleton x})
    ))
  -- reverse(l₁++l₂) = reverse(l₂)++reverse(l₁)
  -- reverse(l₁++l₂)++(singleton x) = (reverse(l₂)++reverse(l₁))++(singleton x)
  -- reverse(l₁++l₂)++(singleton x) = reverse(l₂)++(reverse(l₁)++(singleton x))
  -- reverse(l₁++l₂)++(singleton x) = reverse(l₂)++reverse(x ⊰ l₁)
  -- reverse(x ⊰ (l₁++l₂)) = reverse(l₂)++reverse(x ⊰ l₁)
  -- reverse((x ⊰ l₁)++l₂) = reverse(l₂)++reverse(x ⊰ l₁)

-- reverse (x ⊰ l) = (reverse l) ++ (singleton x)
-- _++_ ∅ b = b
-- _++_ (elem ⊰ rest) b = elem ⊰ (rest ++ b)
