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
private variable f : A → B
private variable P : T → Bool

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
permutation-mapping : (l₁ permutes l₂) → (𝕟(length(l₁)) → 𝕟(length(l₂)))
permutation-mapping empty                = id
permutation-mapping (prepend p) 𝟎        = 𝟎
permutation-mapping (prepend p) (𝐒 n)    = 𝐒(permutation-mapping p n)
permutation-mapping swap        𝟎        = 𝐒(𝟎)
permutation-mapping swap        (𝐒 𝟎)    = 𝟎
permutation-mapping swap        (𝐒(𝐒 n)) = 𝐒 (𝐒 n)
permutation-mapping (trans p q)          = permutation-mapping q ∘ permutation-mapping p

-- TODO: It should be possible to make (_permutes_) the morphism of a category with some correct notion of equivalence (maybe trans swap swap ≡ refl for example?). Then permutation-mapping would be an instance of Functor(length) for the ((_→_) on₂ 𝕟) category?

module Proofs where
  open import Data.List.Proofs
  open import Data.List.Equiv.Id
  open import Lang.Inspect
  open import Logic.Predicate
  open import Numeral.Natural
  open import Numeral.Finite.Proofs
  open import Relator.Equals
  open import Relator.Equals.Proofs
  open import Structure.Function.Domain
  open import Structure.Function.Domain.Proofs
  import      Structure.Function.Names as Names
  open import Structure.Function.Proofs
  open import Structure.Function
  import      Structure.Operator.Names as Names
  open import Structure.Operator.Properties
  open import Structure.Operator
  import      Structure.Relator.Names as Names
  open import Structure.Relator.Equivalence
  open import Structure.Relator.Properties
  open import Structure.Setoid using (Equiv)
  open import Syntax.Function
  open import Syntax.Transitivity

  module _ {ℓ} (P : ∀{l₁ l₂ : List(T)} → (l₁ permutes l₂) → Type{ℓ})
    (pe : P(empty))
    (pp : ∀{x}{l₁ l₂}{p : l₁ permutes l₂} → P(p) → P(prepend{x = x} p))
    (ps : ∀{x y}{l} → P(swap{x = x}{y = y}{l = l}))
    (pt : ∀{l₁ l₂ l₃}{p : l₁ permutes l₂}{q : l₂ permutes l₃} → P(p) → P(q) → P(trans p q))
    where

    permutes-elim : ∀{l₁ l₂} → (p : l₁ permutes l₂) → P(p)
    permutes-elim empty       = pe
    permutes-elim (prepend p) = pp(permutes-elim p)
    permutes-elim swap        = ps
    permutes-elim (trans p q) = pt (permutes-elim p) (permutes-elim q)

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

  permutes-equiv : Equiv(List(T))
  Equiv._≡_         permutes-equiv = _permutes_
  Equiv.equivalence permutes-equiv = permutes-equivalence

  -- If permutation relation had empty, prepend and trans-swap
  module _ where
    swap-from-trans-swap : (x ⊰ y ⊰ l) permutes (y ⊰ x ⊰ l)
    swap-from-trans-swap = trans-swap(reflexivity(_permutes_))

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

  permutes-prepend-function : Function ⦃ permutes-equiv ⦄ ⦃ permutes-equiv ⦄ (List.prepend x)
  permutes-prepend-function = intro prepend

  permutes-postpend-function : Function ⦃ permutes-equiv ⦄ ⦃ permutes-equiv ⦄ (postpend x)
  permutes-postpend-function = intro proof where
    proof : (l₁ permutes l₂) → (postpend x l₁) permutes (postpend x l₂)
    proof empty       = prepend empty
    proof (prepend x) = prepend (proof x)
    proof swap        = swap
    proof (trans x y) = trans (proof x) (proof y)

  postpend-prepend-permutes : (postpend x l) permutes (List.prepend x l)
  postpend-prepend-permutes {l = ∅} = prepend empty
  postpend-prepend-permutes {l = x ⊰ l} = trans (prepend postpend-prepend-permutes) swap

  permutes-reverse : (reverse l) permutes l
  permutes-reverse {l = ∅} = empty
  permutes-reverse {l = x ⊰ l} = trans (Function.congruence ⦃ _ ⦄ ⦃ _ ⦄ permutes-postpend-function(permutes-reverse {l = l})) postpend-prepend-permutes

  permutes-length-function : Function ⦃ permutes-equiv {T = T} ⦄ (length)
  permutes-length-function = intro proof where
    proof : (l₁ permutes l₂) → (length l₁ ≡ length l₂)
    proof empty       = [≡]-intro
    proof (prepend p) = congruence₁(𝐒) (proof p)
    proof swap        = [≡]-intro
    proof (trans p q) = transitivity(_≡_) (proof p) (proof q)

  permutes-countᵣ-function : Function ⦃ permutes-equiv ⦄ (count P)
  permutes-countᵣ-function = intro proof where
    proof : (l₁ permutes l₂) → (count P l₁ ≡ count P l₂)
    proof empty = [≡]-intro
    proof {l₁ = x₁ ⊰ l₁} {P = P} (prepend {x = x} p) with P(x)
    ... | 𝑇 = [≡]-with 𝐒(proof {l₁ = l₁} {P = P} p)
    ... | 𝐹 = proof {l₁ = l₁} {P = P} p
    proof {P = P} (swap {x = x} {y = y}) with P(x) | P(y)
    ... | 𝑇 | 𝑇 = [≡]-intro
    ... | 𝑇 | 𝐹 = [≡]-intro
    ... | 𝐹 | 𝑇 = [≡]-intro
    ... | 𝐹 | 𝐹 = [≡]-intro
    proof (trans p q) = proof p 🝖 proof q

  permutes-satisfiesAny-functionᵣ : Function ⦃ permutes-equiv ⦄ (satisfiesAny f)
  permutes-satisfiesAny-functionᵣ = intro proof where
    proof : (l₁ permutes l₂) → (satisfiesAny f l₁ ≡ satisfiesAny f l₂)
    proof empty = [≡]-intro
    proof {f = f} (prepend{x = x} p) with f(x)
    ... | 𝑇 = [≡]-intro
    ... | 𝐹 = proof p
    proof {l₁ = x ⊰ y ⊰ l₁}{y ⊰ x ⊰ l₂}{f = f} (swap{x = x}{y = y}) with f(x) | f(y) | inspect f(x) | inspect f(y)
    ... | 𝑇 | 𝑇 | intro _ | intro _ = [≡]-intro
    ... | 𝑇 | 𝐹 | intro _ | intro _ with 𝑇 ← f(x) = [≡]-intro
    ... | 𝐹 | 𝑇 | intro _ | intro _ with 𝑇 ← f(y) = [≡]-intro
    ... | 𝐹 | 𝐹 | intro _ | intro _ with 𝐹 ← f(x) | 𝐹 ← f(y)= reflexivity(_≡_)
    proof (trans p q) = proof p 🝖 proof q

  {- TODO
  permutes-countₗ : (∀{P} → count P l₁ ≡ count P l₂) → (l₁ permutes l₂)
  permutes-countₗ {l₁ = ∅} {l₂ = ∅} p = empty
  permutes-countₗ {l₁ = ∅} {l₂ = x ⊰ l₂} p with () ← p{const 𝑇}
  permutes-countₗ {l₁ = x ⊰ l₁} {l₂ = ∅} p with () ← p{const 𝑇}
  permutes-countₗ {l₁ = x ⊰ l₁} {l₂ = x₁ ⊰ l₂} p = {!!} -- TODO: The rest of the cases from _permutes_. Maybe decidable equality on the items are required?
  -}

  permutes-[++]-function : BinaryOperator ⦃ permutes-equiv ⦄ ⦃ permutes-equiv ⦄ ⦃ permutes-equiv ⦄ (_++_ {T = T})
  permutes-[++]-function = binaryOperator-from-function ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄ ⦃ \{l} → intro(R{l = l}) ⦄ ⦃ intro L ⦄ where
    L : Names.Congruence₁ ⦃ permutes-equiv ⦄ ⦃ permutes-equiv ⦄ (_++ l)
    L {l = l} empty = reflexivity(_permutes_)
    L {l = l} (prepend l12) = prepend (L {l = l} l12)
    L {l = l} swap = swap
    L {l = l} (trans l13 l32) = transitivity(_permutes_) (L {l = l} l13) (L {l = l} l32)

    R : Names.Congruence₁ ⦃ permutes-equiv ⦄ ⦃ permutes-equiv ⦄ (l ++_)
    R {l = ∅}     l12 = l12
    R {l = x ⊰ l} l12 = prepend (R {l = l} l12)

  permutes-[++]-commutativity : Commutativity ⦃ permutes-equiv {T = T} ⦄ (_++_)
  permutes-[++]-commutativity = intro(\{l₁}{l₂} → proof{l₁}{l₂}) where
    proof : Names.Commutativity ⦃ permutes-equiv ⦄ (_++_)
    proof {∅}      {l₂} rewrite identityᵣ(_++_)(∅) {l₂} = reflexivity(_permutes_)
    proof {x ⊰ l₁} {l₂} =
      (x ⊰ l₁) ++ l₂        🝖[ _permutes_ ]-[]
      x ⊰ (l₁ ++ l₂)        🝖[ _permutes_ ]-[ prepend (proof {l₁} {l₂}) ]
      x ⊰ (l₂ ++ l₁)        🝖[ _permutes_ ]-[]
      (x ⊰ l₂) ++ l₁        🝖[ _permutes_ ]-[ BinaryOperator.congruence ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄ permutes-[++]-function (postpend-prepend-permutes {l = l₂}) (reflexivity(_permutes_)) ]-sym
      (postpend x l₂) ++ l₁ 🝖[ _permutes_ ]-[ sub₂(_≡_)(_permutes_) ([++]-middle-prepend-postpend {l₁ = l₂}{l₂ = l₁}) ]
      l₂ ++ (x ⊰ l₁)        🝖[ _permutes_ ]-end

  permutes-empty-not-empty : ¬(∅ permutes (x ⊰ l))
  permutes-empty-not-empty (trans {l₂ = ∅}     p q) = permutes-empty-not-empty q
  permutes-empty-not-empty (trans {l₂ = _ ⊰ _} p q) = permutes-empty-not-empty p

  permutes-map : ∀{f : A → B} → Function ⦃ permutes-equiv ⦄ ⦃ permutes-equiv ⦄ (map f)
  permutes-map {f = f} = intro proof where
    proof : Names.Congruence₁ ⦃ permutes-equiv ⦄ ⦃ permutes-equiv ⦄ (map f)
    proof empty       = empty
    proof (prepend p) = prepend (proof p)
    proof swap        = swap
    proof (trans p q) = trans(proof p) (proof q)

  permutes-on-empty : (l permutes ∅) → (l ≡ ∅)
  permutes-on-empty empty = [≡]-intro
  permutes-on-empty (trans p q)
    rewrite permutes-on-empty q
    rewrite permutes-on-empty p
    = [≡]-intro

  permutes-on-singleton : (l permutes (singleton x)) → (l ≡ singleton x)
  permutes-on-singleton (prepend empty) = [≡]-intro
  permutes-on-singleton (prepend (trans p q))
    rewrite permutes-on-empty q
    rewrite permutes-on-empty p
    = [≡]-intro
  permutes-on-singleton (trans p q)
    rewrite permutes-on-singleton q
    rewrite permutes-on-singleton p
    = [≡]-intro

  permutes-insertIn : ∀{n} → ((insertIn x l n) permutes (x ⊰ l))
  permutes-insertIn {n = 𝟎}               = reflexivity(_permutes_)
  permutes-insertIn {l = x ⊰ l} {n = 𝐒 n} = trans (prepend (permutes-insertIn {n = n})) swap

module InsertionPermutation where
  data _insertion-permutes_ {ℓ} : List{ℓ}(T) → List{ℓ}(T) → Stmt{Lvl.𝐒(ℓ)} where
    empty : ∅ insertion-permutes (∅ {T = T})
    ins : (n : 𝕟₌(length l₁)) → (l₁ insertion-permutes l₂) → ((insertIn x l₁ n) insertion-permutes (x ⊰ l₂))

  open import Data.List.Proofs.Length
  open import Relator.Equals.Proofs
  open import Structure.Relator

  insertion-permutation-mapping : (l₁ insertion-permutes l₂) → (𝕟(length(l₁)) → 𝕟(length(l₂)))
  insertion-permutation-mapping empty              ()
  insertion-permutation-mapping (ins 𝟎 p)          𝟎              = 𝟎
  insertion-permutation-mapping (ins 𝟎 p)          (𝐒 i)          = 𝐒(insertion-permutation-mapping p i)
  insertion-permutation-mapping (ins {l₁ = x ⊰ l₁} (𝐒 n) p) 𝟎     = 𝟎
  insertion-permutation-mapping (ins {l₁ = x ⊰ l₁} (𝐒 n) p) (𝐒 i) = 𝐒(insertion-permutation-mapping p (substitute₁(𝕟) (length-insertIn {l = l₁} {n = n}) i))

  open import Data using ()
  open import Numeral.Natural
  open import Relator.Equals
  open import Syntax.Number

  insertion-permutes-prepend : (l₁ insertion-permutes l₂) → ((x ⊰ l₁) insertion-permutes (x ⊰ l₂))
  insertion-permutes-prepend p = ins 𝟎 p

  insertion-permutes-refl : l insertion-permutes l
  insertion-permutes-refl {l = ∅} = empty
  insertion-permutes-refl {l = x ⊰ l} = insertion-permutes-prepend insertion-permutes-refl

  insertion-permutes-swap : (x ⊰ y ⊰ l) insertion-permutes (y ⊰ x ⊰ l)
  insertion-permutes-swap = ins 1 (insertion-permutes-prepend insertion-permutes-refl)

  insertion-permutes-to-permutes : (l₁ insertion-permutes l₂) → (l₁ permutes l₂)
  insertion-permutes-to-permutes empty     = empty
  insertion-permutes-to-permutes (ins n p) = trans Proofs.permutes-insertIn (prepend (insertion-permutes-to-permutes p))

  insertion-permutes-flipped-ins : ∀{n} → (l₁ insertion-permutes l₂) → ((x ⊰  l₁) insertion-permutes (insertIn x l₂ n))
  insertion-permutes-flipped-ins {n = 𝟎}   empty      = insertion-permutes-refl
  insertion-permutes-flipped-ins {n = 𝟎}   (ins k p)  = insertion-permutes-prepend (ins k p)
  insertion-permutes-flipped-ins {n = 𝐒 n} (ins k p) = ins (𝐒 k) (insertion-permutes-flipped-ins {n = n} p)

  insertion-permutes-sym : (l₁ insertion-permutes l₂) → (l₂ insertion-permutes l₁)
  insertion-permutes-sym empty = empty
  insertion-permutes-sym (ins n p) = insertion-permutes-flipped-ins(insertion-permutes-sym p)

  {-
  insertion-permutes-trans : (l₁ insertion-permutes l₂) → (l₃ insertion-permutes l₂) → (l₁ insertion-permutes l₃)
  ins2 : ∀{n₁ n₂} → (l₁ insertion-permutes l₂) → ((insertIn x l₁ n₁) insertion-permutes (insertIn x l₂ n₂))

  ins2 {l₁ = l₁} {l₂} {n₁ = n₁} {𝟎} p = ins n₁ p
  ins2 {l₁ = .(insertIn x _ n)} {x ⊰ l₂} {n₁ = 𝟎} {𝐒 n₂} (ins n p) = insertion-permutes-trans (insertion-permutes-prepend (ins n p)) (ins(𝐒 n₂) insertion-permutes-refl)
  ins2 {l₁ = .(insertIn x _ n)} {x ⊰ l₂} {n₁ = 𝐒 n₁} {𝐒 n₂} (ins n p) = {!!}

  insertion-permutes-trans empty     empty     = empty
  insertion-permutes-trans (ins m p) (ins n q) = {!!}
  -- ins2(insertion-permutes-trans p q)
  -}

  {-
  insertion-permutation-mapping-correctness : (p : (l₁ insertion-permutes l₂)) → Proofs.PermutationMappingCorrectness l₁ l₂ (insertion-permutation-mapping p)
  insertion-permutation-mapping-correctness (ins {l₁ = ∅} 𝟎 p) {𝟎} = [≡]-intro
  insertion-permutation-mapping-correctness (ins {l₁ = x ⊰ l₁} 𝟎 p) {𝟎} = [≡]-intro
  insertion-permutation-mapping-correctness (ins {l₁ = x ⊰ l₁} 𝟎 p) {𝐒 i} = insertion-permutation-mapping-correctness p
  insertion-permutation-mapping-correctness (ins {l₁ = x ⊰ l₁} (𝐒 n) p) {𝟎} = {!!}
  insertion-permutation-mapping-correctness (ins {l₁ = x ⊰ l₁} (𝐒 n) p) {𝐒 i} = {!!}
  -}

  -- test : (p : (l₁ insertion-permutes l₂)) → (∀{i} → (index l₁(insertion-permutation-mapping p i) ≡ index l₂(i)))
  -- test p = ?

  {-
  open import Data.Boolean.Stmt
  open import Numeral.Finite.Oper.Comparisons
  test : ∀{l : List(T)}{n₁ : 𝕟(𝐒(length l))}{n₂ : 𝕟(𝐒(length (insertIn y l n₁)))} → IsTrue(n₁ >? n₂) → (insertIn y (insertIn x l n₁) n₂ ≡ insertIn x (insertIn y l n₁) n₂)
  test p = {!!}
  -}

  {-
  ins2 : ∀{n₁ n₂} → (l₁ insertion-permutes l₂) → ((insertIn x l₁ n₁) insertion-permutes (insertIn x l₂ n₂))
  ins2 {n₁ = 𝟎} {𝟎} empty = insertion-permutes-refl
  ins2 {n₁ = n₁} {𝟎} (ins n p) = ins n₁ (ins n p)
  ins2 {x = x} {n₁ = n₁} {𝐒 n₂} (ins {x = y} n p) = {!(ins2 {x = x}{n₁ = n}{n₂ = n₂} p)!}

  insertion-permutes-trans : (l₁ insertion-permutes l₂) → (l₃ insertion-permutes l₂) → (l₁ insertion-permutes l₃)
  insertion-permutes-trans empty empty = empty
  insertion-permutes-trans (ins m p) (ins n q) = {!!}
  -}

  {-
  test : ∀{n} → (l₁ insertion-permutes (y ⊰ insertIn x l₂ n)) → (l₁ insertion-permutes (x ⊰ insertIn y l₂ n))
  test {l₂ = l₂} (ins {l₁ = l₁} n p) = {!!}

  ins2 : ∀{n₁ n₂} → (l₁ insertion-permutes l₂) → ((insertIn x l₁ n₁) insertion-permutes (insertIn x l₂ n₂))
  ins2 {n₁ = n₁} {𝟎} p = ins n₁ p
  ins2 {n₁ = n₁} {𝐒 n₂} (ins {x = x} n p) = test(ins n₁ (ins2{x = x}{n}{n₂} p))

  -- insertIn x₁ (insertIn x l₁ n) n₁
  -- x ⊰ insertIn x₁ l₂ n₂

  tr : (l₁ insertion-permutes l₂) → (l₃ insertion-permutes l₂) → (l₁ insertion-permutes l₃)
  tr {l₂ = ∅}       empty      empty      = empty
  tr {l₂ = x₂ ⊰ l₂} (ins n₁ p) (ins n₂ q) = ins2(tr p q)

  sym : (l₁ insertion-permutes l₂) → (l₂ insertion-permutes l₁)
  sym = tr insertion-permutes-refl
  -}
