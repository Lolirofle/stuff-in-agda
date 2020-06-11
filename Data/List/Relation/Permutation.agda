module Data.List.Relation.Permutation where

import      Data
open import Data.List
open import Data.List.Functions renaming (module LongOper to List)
open import Data.List.Relation
open import Functional using (id ; _∘_)
open import Logic.Propositional
open import Logic
import      Lvl
open import Numeral.Finite
open import Syntax.Function
open import Type

private variable ℓ : Lvl.Level
private variable T A B : Type{ℓ}
private variable l l₁ l₂ l₃ l₄ : List(T)
private variable x y z : T

-- The relation for two lists that are permutations of each other.
-- This means that they contain the same elements and the same number of them but possibly in a different order.
-- Or in other words, the first list is a reordered list of the second.
data _permutes_ {ℓ} : List{ℓ}(T) → List{ℓ}(T) → Stmt{Lvl.𝐒(ℓ)} where
  empty   : ∅ permutes (∅ {T = T})
  prepend : (l₁ permutes l₂) → ((x ⊰ l₁) permutes (x ⊰ l₂))
  swap    : (x ⊰ y ⊰ l) permutes (y ⊰ x ⊰ l)
  trans   : (l₁ permutes l₂) → (l₂ permutes l₃) → (l₁ permutes l₃)

trans-swap : (l₁ permutes l₂) → ((x ⊰ y ⊰ l₁) permutes (y ⊰ x ⊰ l₂))
trans-swap p = trans swap (prepend (prepend p))

-- TODO
-- _partition-of_ : List(List(T)) → List(T) → Stmt
-- p partition-of l = (foldᵣ (x ↦ ¬ Empty(x) ∧_) Data.Unit p) ∧ (concat(p) permutes l)

-- The permutation as a function between the permutated elements' indices.
-- Example:
--   p : [a,b,c,d,e,f] permutes [a,f,e,d,b,c]
--   map(permutation-mapping(p)) [0,1,2,3,4,5] = [0,4,5,3,2,1]
permutation-mapping : (l₁ permutes l₂) → 𝕟(length(l₁)) → 𝕟(length(l₂))
permutation-mapping empty                = id
permutation-mapping (prepend p) 𝟎        = 𝟎
permutation-mapping (prepend p) (𝐒 n)    = 𝐒(permutation-mapping p n)
permutation-mapping swap        𝟎        = 𝐒(𝟎)
permutation-mapping swap        (𝐒 𝟎)    = 𝟎
permutation-mapping swap        (𝐒(𝐒 n)) = 𝐒 (𝐒 n)
permutation-mapping (trans p q)          = permutation-mapping q ∘ permutation-mapping p

module Proofs where
  open import Data.List.Proofs
  open import Logic.Predicate
  open import Numeral.Natural
  open import Numeral.Finite.Proofs
  open import Relator.Equals
  open import Relator.Equals.Proofs
  open import Structure.Function.Domain
  open import Structure.Function.Domain.Proofs
  import      Structure.Function.Names as Names
  open import Structure.Function
  import      Structure.Relator.Names as Names
  open import Structure.Relator.Equivalence
  open import Structure.Relator.Properties
  open import Syntax.Function
  open import Syntax.Transitivity

  instance
    permutes-reflexivity : Reflexivity(_permutes_ {T = T})
    permutes-reflexivity = intro proof where
      proof : Names.Reflexivity(_permutes_)
      proof {∅}     = empty
      proof {_ ⊰ _} = prepend proof

  instance
    permutes-symmetry : Symmetry(_permutes_ {T = T})
    permutes-symmetry = intro proof where
      proof : Names.Symmetry(_permutes_)
      proof empty       = empty
      proof (prepend p) = prepend (proof p)
      proof swap        = swap
      proof (trans p q) = trans (proof q) (proof p)

  instance
    permutes-transitivity : Transitivity(_permutes_ {T = T})
    permutes-transitivity = intro trans

  instance
    permutes-equivalence : Equivalence(_permutes_ {T = T})
    permutes-equivalence = intro

  permutation-mapping-correctness : (p : (l₁ permutes l₂)) → ∀{i} → (index l₁(i) ≡ index l₂(permutation-mapping p i))
  permutation-mapping-correctness empty                 = reflexivity(_≡_)
  permutation-mapping-correctness (prepend p) {𝟎}       = reflexivity(_≡_)
  permutation-mapping-correctness (prepend p) {𝐒 i}     = permutation-mapping-correctness p {i}
  permutation-mapping-correctness swap        {𝟎}       = reflexivity(_≡_)
  permutation-mapping-correctness swap        {𝐒 𝟎}     = reflexivity(_≡_)
  permutation-mapping-correctness swap        {𝐒 (𝐒 i)} = reflexivity(_≡_)
  permutation-mapping-correctness (trans p q)           = permutation-mapping-correctness p 🝖 permutation-mapping-correctness q

  instance
    permutation-mapping-injective : ∀{p : (l₁ permutes l₂)} → Injective(permutation-mapping p)
    permutation-mapping-injective {p = p} = intro(proof p) where
      proof : (p : (l₁ permutes l₂)) → Names.Injective(permutation-mapping p)
      proof (prepend p) {𝟎}   {𝟎}   eq = [≡]-intro
      proof (prepend p) {𝐒 x} {𝐒 y} eq = congruence₁(𝐒) (proof p (injective(𝐒) ⦃ [𝐒]-injective ⦄ eq))
      proof swap {𝟎}       {𝟎}       eq = [≡]-intro
      proof swap {𝟎}       {𝐒 (𝐒 y)} ()
      proof swap {𝐒 (𝐒 x)} {𝟎}       ()
      proof swap {𝐒 𝟎}     {𝐒 𝟎}     eq = [≡]-intro
      proof swap {𝐒 (𝐒 x)} {𝐒 (𝐒 y)} eq = eq
      proof (trans p q) = proof p ∘ proof q

  instance
    permutation-mapping-surjective : ∀{p : (l₁ permutes l₂)} → Surjective(permutation-mapping p)
    permutation-mapping-surjective {p = p} = intro(proof p) where
      proof : (p : (l₁ permutes l₂)) → Names.Surjective(permutation-mapping p)
      ∃.witness (proof p {y}) = permutation-mapping(symmetry(_permutes_) p) y
      ∃.proof (proof (prepend p) {𝟎})   = [≡]-intro
      ∃.proof (proof (prepend p) {𝐒 y}) = congruence₁(𝐒) (∃.proof (proof p {y}))
      ∃.proof (proof swap {𝟎})       = [≡]-intro
      ∃.proof (proof swap {𝐒 𝟎})     = [≡]-intro
      ∃.proof (proof swap {𝐒 (𝐒 y)}) = [≡]-intro
      ∃.proof (proof (trans p q) {y}) =
        permutation-mapping (trans p q) (∃.witness (proof (trans p q))) 🝖[ _≡_ ]-[]
        (permutation-mapping (trans p q) ∘ permutation-mapping(symmetry(_permutes_) p) ∘ permutation-mapping (symmetry(_permutes_) q)) y 🝖[ _≡_ ]-[]
        (permutation-mapping q ∘ permutation-mapping p ∘ permutation-mapping(symmetry(_permutes_) p) ∘ permutation-mapping (symmetry(_permutes_) q)) y 🝖[ _≡_ ]-[ congruence₁(permutation-mapping q) (∃.proof (proof p {_})) ]
        (permutation-mapping q ∘ permutation-mapping (symmetry(_permutes_) q)) y 🝖[ _≡_ ]-[ ∃.proof (proof q {y}) ]
        y 🝖[ _≡_ ]-end

  instance
    permutation-mapping-bijective : ∀{p : (l₁ permutes l₂)} → Bijective(permutation-mapping p)
    permutation-mapping-bijective {p = p} = injective-surjective-to-bijective(permutation-mapping p) ⦃ permutation-mapping-injective {p = p} ⦄ ⦃ permutation-mapping-surjective {p = p} ⦄

  permutes-with-postpend : (l₁ permutes l₂) → (postpend x l₁) permutes (postpend x l₂)
  permutes-with-postpend empty       = prepend empty
  permutes-with-postpend (prepend x) = prepend (permutes-with-postpend x)
  permutes-with-postpend swap        = swap
  permutes-with-postpend (trans x y) = trans (permutes-with-postpend x) (permutes-with-postpend y)

  postpend-prepend-permutes : (postpend x l) permutes (List.prepend x l)
  postpend-prepend-permutes {l = ∅} = prepend empty
  postpend-prepend-permutes {l = x ⊰ l} = trans (prepend postpend-prepend-permutes) swap

  permutes-reverse : (reverse l) permutes l
  permutes-reverse {l = ∅} = empty
  permutes-reverse {l = x ⊰ l} = trans (permutes-with-postpend(permutes-reverse {l = l})) postpend-prepend-permutes

  permutes-length : (l₁ permutes l₂) → (length l₁ ≡ length l₂)
  permutes-length empty       = [≡]-intro
  permutes-length (prepend p) = congruence₁(𝐒) (permutes-length p)
  permutes-length swap        = [≡]-intro
  permutes-length (trans p q) = transitivity(_≡_) (permutes-length p) (permutes-length q)

  -- permutes-count : (l₁ permutes l₂) → (count a l₁ ≡ count a l₂)

  permutes-with-[++]ₗ : (l₁ permutes l₂) → ((l₁ ++ l) permutes (l₂ ++ l))
  permutes-with-[++]ₗ {l = l} empty = reflexivity(_permutes_)
  permutes-with-[++]ₗ {l = l} (prepend l12) = prepend (permutes-with-[++]ₗ {l = l} l12)
  permutes-with-[++]ₗ {l = l} swap = swap
  permutes-with-[++]ₗ {l = l} (trans l13 l32) = transitivity(_permutes_) (permutes-with-[++]ₗ {l = l} l13) (permutes-with-[++]ₗ {l = l} l32)

  permutes-with-[++]ᵣ : (l₁ permutes l₂) → ((l ++ l₁) permutes (l ++ l₂))
  permutes-with-[++]ᵣ {l = ∅}     l12 = l12
  permutes-with-[++]ᵣ {l = x ⊰ l} l12 = prepend (permutes-with-[++]ᵣ {l = l} l12)

  permutes-with-[++] : (l₁ permutes l₃) → (l₂ permutes l₄) → ((l₁ ++ l₂) permutes (l₃ ++ l₄))
  permutes-with-[++] {l₃ = l₃} {l₂ = l₂} l13 l24 = transitivity(_permutes_) (permutes-with-[++]ₗ {l = l₂} l13) (permutes-with-[++]ᵣ {l = l₃} l24)

  permutes-swap-[++] : ((l₁ ++ l₂) permutes (l₂ ++ l₁))
  permutes-swap-[++] {l₁ = ∅}      {l₂ = l₂} = reflexivity(_permutes_)
  permutes-swap-[++] {l₁ = x ⊰ l₁} {l₂ = l₂} =
    (x ⊰ l₁) ++ l₂        🝖[ _permutes_ ]-[]
    x ⊰ (l₁ ++ l₂)        🝖[ _permutes_ ]-[ prepend (permutes-swap-[++] {l₁ = l₁} {l₂ = l₂}) ]
    x ⊰ (l₂ ++ l₁)        🝖[ _permutes_ ]-[]
    (x ⊰ l₂) ++ l₁        🝖[ _permutes_ ]-[ permutes-with-[++]ₗ {l = l₁} (postpend-prepend-permutes {l = l₂}) ]-sym
    (postpend x l₂) ++ l₁ 🝖[ _permutes_ ]-[ sub₂(_≡_)(_permutes_) ([++]-middle-prepend-postpend {l₁ = l₂}{l₂ = l₁}) ]
    l₂ ++ (x ⊰ l₁)        🝖[ _permutes_ ]-end
