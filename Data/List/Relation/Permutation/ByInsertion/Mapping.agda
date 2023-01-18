module Data.List.Relation.Permutation.ByInsertion.Mapping where

open import BidirectionalFunction using (_↔_ ; intro)
open import Data.List using (List)
open import Data.List.Functions as List using (length ; insertIn)
open import Data.List.Proofs.Length
open import Data.List.Relation.Permutation.ByInsertion
open import Data.List.Relation.Permutation.ByInsertion.Oper
open import Functional using (id)
open import Logic.Propositional
open import Numeral.Finite.Bound
open import Numeral.Finite.Bound.Substitution as 𝕟 using (𝕟-relator)
open import Relator.Equals.Proofs
open import Structure.Relator
import      Lvl
open import Numeral.Finite
open import Type

private variable ℓ : Lvl.Level
private variable T : Type{ℓ}
private variable l₁ l₂ : List(T)
private variable p : l₁ permutes l₂

permutationMapping : (l₁ permutes l₂) → (𝕟(length(l₁)) ← 𝕟(length(l₂)))
permutationMapping empty                    = id
permutationMapping (ins{l₁} n      p) 𝟎     = substitute₁ₗ(𝕟) ⦃ 𝕟-relator ⦄ (length-insertIn {l = l₁} {n = n}) n
permutationMapping (ins{l₁} 𝟎      p) (𝐒 i) = 𝐒(permutationMapping p i)
permutationMapping (ins{l₁} (𝐒(n)) p) (𝐒 i) = substitute₁ₗ(𝕟) ⦃ 𝕟-relator ⦄ (length-insertIn {l = l₁} {n = 𝐒 n}) (bound-𝐒(permutationMapping p i))

permutationMappings : (l₁ permutes l₂) → (𝕟(length(l₁)) ↔ 𝕟(length(l₂)))
permutationMappings p = intro(permutationMapping p) (permutationMapping(sym p))

-- permutationMapping-of-sym : ∀{p : l₁ permutes l₂}{i}{n} → ((permutationMapping (sym(flippedIns{x = x} n p)) (permutationMapping(p) n i)) 𝕟.≡ i)
-- permutationMapping-of-sym {p = ins n p} {i} = {!!}

{-
open import BidirectionalFunction
open import Relator.Equals
open import Structure.Function
open import Structure.Function.Domain
import      Structure.Function.Names as Names
open import Syntax.Transitivity

instance
  permutationMapping-injective : Injective(permutationMapping p)
  permutationMapping-injective = intro(\{x}{y} → proof{x = x}{y = y}) where
    proof : Names.Injective(permutationMapping p)
    proof {p = ins n p} {𝟎} {𝟎} xy = [≡]-intro
    proof {p = ins 𝟎 p} {𝐒 x} {𝐒 y} xy = congruence₁(𝐒) (proof{p = p} {!injective(𝐒) xy!})
    proof {p = ins (𝐒 n) p} {𝟎} {𝐒 y} xy = {!!}
    proof {p = ins (𝐒 n) p} {𝐒 x} {𝟎} xy = {!!}
    proof {p = ins (𝐒 n) p} {𝐒 x} {𝐒 y} xy = congruence₁(𝐒) (proof{p = p} {!!})

instance
  permutationMapping-inverses : ∀{p : l₁ permutes l₂} → InversePair(permutationMappings p)
  permutationMapping-inverses{p = p} = intro ⦃ left = intro(L p) ⦄ ⦃ right = intro(R p) ⦄ where
    L : (p : l₁ permutes l₂) → Names.Inverses(permutationMappings p $ᵣ_)(permutationMappings p $ₗ_)
    L (ins{x = x} 𝟎 p) {𝟎} =
      permutationMapping(sym(ins{x = x} 𝟎 p)) (permutationMapping(ins{x = x} 𝟎 p) 𝟎)              🝖[ _≡_ ]-[]
      permutationMapping(flippedIns{x = x} 𝟎 (sym p)) (substitute₁ₗ(𝕟) ⦃ 𝕟-relator ⦄ [≡]-intro 𝟎) 🝖[ _≡_ ]-[ {!!} ]
      permutationMapping(flippedIns{x = x} 𝟎 (sym p)) 𝟎                                           🝖[ _≡_ ]-[ {!!} ]
      permutationMapping(sym(ins{x = x} 𝟎 p)) 𝟎                                                   🝖[ _≡_ ]-[ {!!} ]
      𝟎                                                                                           🝖-end
    L (ins 𝟎 p) {𝐒 i} = {![≡]-intro!}
    L (ins (𝐒 n) p) {𝟎} = {!!}
    L (ins (𝐒 n) p) {𝐒 i} = {!!}

    -- permutationMapping(sym p) (permutationMapping p 𝟎) ≡ 𝟎

    R : (p : l₂ permutes l₁) → Names.Inverses(permutationMappings p $ₗ_)(permutationMappings p $ᵣ_)
    R (ins 𝟎 p) {i} =
      permutationMapping (ins 𝟎 p) (permutationMapping(sym(ins 𝟎 p)) i) 🝖[ _≡_ ]-[ {!!} ]
      i 🝖-end
    R (ins (𝐒 n) p) {i} = {!!}
-}

{-
insertion-permutation-mapping-correctness : (p : (l₁ permutes l₂)) → Proofs.PermutationMappingCorrectness l₁ l₂ (insertion-permutation-mapping p)
insertion-permutation-mapping-correctness (ins {l₁ = ∅} 𝟎 p) {𝟎} = [≡]-intro
insertion-permutation-mapping-correctness (ins {l₁ = x ⊰ l₁} 𝟎 p) {𝟎} = [≡]-intro
insertion-permutation-mapping-correctness (ins {l₁ = x ⊰ l₁} 𝟎 p) {𝐒 i} = insertion-permutation-mapping-correctness p
insertion-permutation-mapping-correctness (ins {l₁ = x ⊰ l₁} (𝐒 n) p) {𝟎} = {!!}
insertion-permutation-mapping-correctness (ins {l₁ = x ⊰ l₁} (𝐒 n) p) {𝐒 i} = {!!}
-}

{-
test0 = 5 ⊰ 4 ⊰ 3 ⊰ 2 ⊰ 1 ⊰ 0 ⊰ ∅
test1 = 0 ⊰ 1 ⊰ 2 ⊰ 3 ⊰ 4 ⊰ 5 ⊰ ∅
test2 = 0 ⊰ 1 ⊰ 3 ⊰ 2 ⊰ 5 ⊰ 4 ⊰ ∅
open import Syntax.Number
testperm01 : test0 permutes test1
testperm01 = ins{x = 0} 5 (ins{x = 1} 4 (ins{x = 2} 3 (ins{x = 3} 2 (ins{x = 4} 1 (ins{x = 5} 0 empty)))))

testperm21 : test2 permutes test1
testperm21 = ins{x = 0} 0 (ins{x = 1} 0 (ins{x = 2} 1 (ins{x = 3} 0 (ins{x = 4} 1 (ins{x = 5} 0 empty)))))

test = {!permutationMapping testperm01 5!}
-}
