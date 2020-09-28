module Data.List.Relation.Permutation where

import      Data
open import Data.Boolean
open import Data.List
open import Data.List.Functions renaming (module LongOper to List)
open import Data.List.Relation
open import Functional using (id ; _∘_ ; const)
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
  open import Structure.Operator.Properties
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

  PermutationMappingCorrectness : (l₁ l₂ : List(T)) → (𝕟(length(l₁)) → 𝕟(length(l₂))) → Stmt
  PermutationMappingCorrectness l₁ l₂ mapping = ∀{i} → (index l₁(i) ≡ index l₂(mapping i))

  permutation-mapping-correctness : (p : (l₁ permutes l₂)) → PermutationMappingCorrectness l₁ l₂ (permutation-mapping p)
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

  permutation-mapping-bijective : ∀{p : (l₁ permutes l₂)} → Bijective(permutation-mapping p)
  permutation-mapping-bijective {p = p} = injective-surjective-to-bijective(permutation-mapping p) ⦃ permutation-mapping-injective {p = p} ⦄ ⦃ permutation-mapping-surjective {p = p} ⦄

  {-
  permutation-from-mapping : (p : 𝕟(length(l₁)) → 𝕟(length(l₂))) ⦃ bij : Bijective(p) ⦄ (correctness : PermutationMappingCorrectness l₁ l₂ p) → (l₁ permutes l₂)
  permutation-from-mapping {l₁ = ∅} {l₂ = ∅} p _ = empty
  permutation-from-mapping {l₁ = ∅} {l₂ = x₂ ⊰ l₂} p _ = {!!}
  permutation-from-mapping {l₁ = x₁ ⊰ l₁} {l₂ = ∅} p _ = {!!}
  permutation-from-mapping {l₁ = x₁ ⊰ l₁} {l₂ = x₂ ⊰ l₂} p correctness with p(𝟎) | correctness{𝟎}
  ... | 𝟎   | [≡]-intro = prepend (permutation-from-mapping (forgetFirstCutoffOfBij p) ⦃ forgetFirstCutoffOfBij-bijective ⦄ {!!}) where
    bijective-equinumerous : ∀{a b}{f : 𝕟(a) → 𝕟(b)} → Bijective(f) → (a ≡ b)
    forgetFirstCutoff : ∀{a} → (𝕟(𝐒(a)) → 𝕟(𝐒(a))) → (𝕟(a) → 𝕟(a))
    forgetFirstCutoff {𝐒(a)} f(x) with f(𝐒(x))
    ... | 𝟎    = 𝟎
    ... | 𝐒(y) = y

    forgetFirstCutoffOfBij : ∀{a b} → (f : 𝕟(𝐒(a)) → 𝕟(𝐒(b))) ⦃ bij : Bijective(f) ⦄ → (𝕟(a) → 𝕟(b))
    forgetFirstCutoffOfBij {𝐒 a} f ⦃ bij ⦄ with [≡]-intro ← bijective-equinumerous bij = forgetFirstCutoff f
    forgetFirstCutoffOfBij-bijective : ∀{a b}{f : 𝕟(𝐒(a)) → 𝕟(𝐒(b))} ⦃ bij : Bijective(f) ⦄ → Bijective(forgetFirstCutoffOfBij f)

    -- proof : ∀{l₁ l₂ : List(T)}{p : 𝕟(length(l₁)) → 𝕟(length(l₂))} → PermutationMappingCorrectness l₁ l₂ (forgetFirstCutoffOfBij p)
    proof : PermutationMappingCorrectness l₁ l₂ (forgetFirstCutoffOfBij p)
    proof {i} =
      index l₁ i                            🝖[ _≡_ ]-[ {!correctness!} ]
      index l₂ (forgetFirstCutoffOfBij p i) 🝖-end 
  ... | 𝐒 w | _ = {!!}
  -}

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

  permutes-countᵣ : (l₁ permutes l₂) → ∀{P} → (count P l₁ ≡ count P l₂)
  permutes-countᵣ empty = [≡]-intro
  permutes-countᵣ {l₁ = x₁ ⊰ l₁} (prepend {x = x} p) {P} with P(x)
  ... | 𝑇 = [≡]-with 𝐒(permutes-countᵣ {l₁ = l₁} p {P})
  ... | 𝐹 = permutes-countᵣ {l₁ = l₁} p {P}
  permutes-countᵣ (swap {x = x} {y = y}) {P} with P(x) | P(y)
  ... | 𝑇 | 𝑇 = [≡]-intro
  ... | 𝑇 | 𝐹 = [≡]-intro
  ... | 𝐹 | 𝑇 = [≡]-intro
  ... | 𝐹 | 𝐹 = [≡]-intro
  permutes-countᵣ (trans p q) = permutes-countᵣ p 🝖 permutes-countᵣ q

  {- TODO
  permutes-countₗ : (∀{P} → count P l₁ ≡ count P l₂) → (l₁ permutes l₂)
  permutes-countₗ {l₁ = ∅} {l₂ = ∅} p = empty
  permutes-countₗ {l₁ = ∅} {l₂ = x ⊰ l₂} p with () ← p{const 𝑇}
  permutes-countₗ {l₁ = x ⊰ l₁} {l₂ = ∅} p with () ← p{const 𝑇}
  permutes-countₗ {l₁ = x ⊰ l₁} {l₂ = x₁ ⊰ l₂} p = {!!} -- TODO: The rest of the cases from _permutes_. Maybe decidable equality on the items are required?
  -}

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
  permutes-swap-[++] {l₁ = ∅}      {l₂ = l₂} rewrite identityᵣ(_++_)(∅) {l₂} = reflexivity(_permutes_)
  permutes-swap-[++] {l₁ = x ⊰ l₁} {l₂ = l₂} =
    (x ⊰ l₁) ++ l₂        🝖[ _permutes_ ]-[]
    x ⊰ (l₁ ++ l₂)        🝖[ _permutes_ ]-[ prepend (permutes-swap-[++] {l₁ = l₁} {l₂ = l₂}) ]
    x ⊰ (l₂ ++ l₁)        🝖[ _permutes_ ]-[]
    (x ⊰ l₂) ++ l₁        🝖[ _permutes_ ]-[ permutes-with-[++]ₗ {l = l₁} (postpend-prepend-permutes {l = l₂}) ]-sym
    (postpend x l₂) ++ l₁ 🝖[ _permutes_ ]-[ sub₂(_≡_)(_permutes_) ([++]-middle-prepend-postpend {l₁ = l₂}{l₂ = l₁}) ]
    l₂ ++ (x ⊰ l₁)        🝖[ _permutes_ ]-end

  permutes-empty-not-empty : ¬(∅ permutes (x ⊰ l))
  permutes-empty-not-empty (trans {l₂ = ∅}     p q) = permutes-empty-not-empty q
  permutes-empty-not-empty (trans {l₂ = _ ⊰ _} p q) = permutes-empty-not-empty p
