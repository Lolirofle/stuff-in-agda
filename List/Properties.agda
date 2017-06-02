module List.Properties{ℓ₁}{ℓ₂} where

import Level as Lvl
open import Functional
open import List
open import Logic.Propositional{ℓ₁ Lvl.⊔ ℓ₂}
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.Properties{ℓ₁}
open import Relator.Equals{ℓ₁}
open import Structure.Operator.Properties
open import Type{ℓ₂}

instance
  [++]-identityₗ : ∀{T} → Identityₗ {ℓ₁}{ℓ₂}{List(T)} (_++_) ∅
  [++]-identityₗ = [≡]-intro

instance
  [++]-identityᵣ : ∀{T} → Identityᵣ {ℓ₁}{ℓ₂}{List(T)} (_++_) ∅
  [++]-identityᵣ {T} = List-induction{ℓ₁}{ℓ₂} base next where
    base : (∅ ++ ∅) ≡ ∅
    base = [≡]-intro

    next : ∀(x : T)(l : List(T)) → ((l ++ ∅) ≡ l) → (((x ⊰ l) ++ ∅) ≡ (x ⊰ l))
    next x _ stmt = [≡]-with-[(list ↦ x ⊰ list)] stmt
    -- (l ++ ∅) ≡ l
    -- x ⊰ (l ++ ∅) ≡ x ⊰ l
    -- (x ⊰ l) ++ ∅ ≡ x ⊰ l

instance
  [++]-associativity : ∀{T} → Associativity {ℓ₁}{ℓ₂} {List(T)} (_++_)
  [++]-associativity {T} {l₀} {l₁} {l₂} = List-induction{ℓ₁}{ℓ₂} base next {l₀} where
    base : ((∅ ++ l₁) ++ l₂) ≡ (∅ ++ (l₁ ++ l₂))
    base = [≡]-intro
    -- l₁++l₂ = l₁++l₂
    -- ∅++(l₁++l₂) = (∅++l₁)++l₂

    next : ∀(x : T)(l : List(T)) → (((l ++ l₁) ++ l₂) ≡ (l ++ (l₁ ++ l₂))) → ((((x ⊰ l) ++ l₁) ++ l₂) ≡ ((x ⊰ l) ++ (l₁ ++ l₂)))
    next x _ stmt = [≡]-with-[(list ↦ x ⊰ list)] stmt
    -- (l++l₁)++l₂ = l++(l₁++l₂)
    -- x ⊰ ((l++l₁)++l₂) = x ⊰ (l++(l₁++l₂))
    -- x ⊰ ((l++l₁)++l₂) = (x ⊰ l)++(l₁++l₂)
    -- (x ⊰ (l++l₁))++l₂ = (x ⊰ l)++(l₁++l₂)
    -- ((x ⊰ l)++l₁)++l₂ = (x ⊰ l)++(l₁++l₂)

instance
  reverse-[++] : ∀{T}{l₁ l₂ : List(T)} → (reverse(l₁ ++ l₂) ≡ reverse(l₂) ++ reverse(l₁))
  reverse-[++] {T} {l₁} {l₂} = List-induction{ℓ₁}{ℓ₂} base next {l₁} where
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
        ([≡]-with-[(list ↦ list ++ (singleton x))] stmt)
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

instance
  length-[∅] : ∀{T : Type} → (length(∅{_}{T}) ≡ 0)
  length-[∅] = [≡]-intro

instance
  length-singleton : ∀{T : Type}{a : T} → (length(singleton(a)) ≡ 1)
  length-singleton = [≡]-intro

instance
  length-[++] : ∀{T}{l₁ l₂ : List(T)} → (length(l₁ ++ l₂) ≡ length(l₁) + length(l₂))
  length-[++] {T} {l₁} {l₂} = List-induction{ℓ₁}{Lvl.𝟎} base next {l₁} where
    base : length(∅ ++ l₂) ≡ length{_}{T}(∅) + length(l₂)
    base = [≡]-symmetry [+]-identityₗ

    next : ∀(x : T)(l : List(T)) → (length(l ++ l₂) ≡ length(l) + length(l₂)) → (length((x ⊰ l) ++ l₂) ≡ length(x ⊰ l) + length(l₂))
    next x l stmt =
      ([≡]-transitivity([∧]-intro
        ([≡]-with-[(len ↦ 𝐒 len)] stmt)
        ([≡]-symmetry([+1]-commutativity {length(l)} {length(l₂)}))
      ))
    -- length(l++l₂) = length(l)+length(l₂)
    -- length(l++l₂) = length(l₂)+length(l)
    -- 𝐒(length(l++l₂)) = 𝐒(length(l₂)+length(l))
    -- 𝐒(length(l++l₂)) = length(l₂)+𝐒(length(l))
    -- 𝐒(length(l++l₂)) = 𝐒(length(l))+length(l₂)
    -- length(x ⊰ (l++l₂)) = length(x ⊰ l)+length(l₂) //TODO: Is this step really okay? 𝐒 cannot uniquely identify that x was the precedant

  -- TODO: length(reverse(l)) = length(l)
  -- length-reverse : ∀{ℓ T}{l : List{ℓ}(T)} → length(reverse(l)) ≡ length(l)
  -- length-reverse {ℓ} {T} = List-induction base next where
  --   base : length{ℓ}{T}(reverse(∅)) ≡ length{ℓ}{T}(∅)
  --   base = [≡]-intro
  -- 
  --   next : ∀(x : T)(l : List(T)) → (length(reverse(l)) ≡ length(l)) → (length(reverse(x ⊰ l)) ≡ length(x ⊰ l))
  --   next x l stmt =
  --     ([≡]-transitivity([∧]-intro
  --       ([≡]-symmetry(length-[++] {ℓ} {T} {singleton(x)} {reverse(l)}))
  --       (([≡]-with-[ 𝐒 ] stmt))
  --     ))
  --   -- length(reverse(l)) = length(l)
  --   -- 𝐒(length(reverse(l))) = 𝐒(length(l))
  --   -- 𝐒(length(reverse(l))) = length(x⊰l)
  --   -- length(x⊰reverse(l)) = length(x⊰l)
  --   -- length((x⊰ε)++reverse(l)) = length(x⊰l)
  --   -- length(x⊰ε)+length(reverse(l)) = length(x⊰l)
  --   -- length(reverse(l))+length(x⊰ε) = length(x⊰l)
  --   -- length(reverse(l)++x⊰ε) = length(x⊰l)
  --   -- length(reverse(l)++singleton(x)) = length(x⊰l)

-- TODO: Empty list is prefix and suffix of everything
-- TODO: Whole list is prefix and suffix of everything
-- TODO: length(repeat(l)(n)) = n
-- TODO: length(multiply(l)(n)) = n ⋅ length(l)
-- TODO: multiply(singleton(l))(n) = repeat(l)(n)
-- TODO: reverse(reverse(l)) = l
