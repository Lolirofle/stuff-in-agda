module Data.List.Relation.Permutation.Proofs where

import      Data
open import Data.Boolean
open import Data.List
open import Data.List.Functions renaming (module LongOper to List)
open import Data.List.Relation
open import Data.List.Relation.Permutation
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
open import Structure.Relator
import      Structure.Relator.Names as Names
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Structure.Relator.Properties.Proofs
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

permutes-map-injective : ∀{f : A → B} → ⦃ inj : Injective(f) ⦄ → Injective ⦃ permutes-equiv ⦄ ⦃ permutes-equiv ⦄ (map f)
permutes-map-injective {f = f} = intro proof where
  Pred = \{mx my} (_ : mx permutes my) → ∀{x y} → (mx ≡ map f(x)) → (my ≡ map f(y)) → x permutes y
  pe : Pred(empty)
  pe {∅} {∅} ex ey = empty

  pp : ∀{x}{l₁ l₂}{p : l₁ permutes l₂} → Pred(p) → Pred(prepend{x = x} p)
  pp {x}{ml₁}{ml₂} p {x₁ ⊰ l₁}{x₂ ⊰ l₂} e1 e2
    rewrite injective(f) (symmetry(_≡_) ([∧]-elimₗ ([⊰]-general-cancellation e1)) 🝖 [∧]-elimₗ ([⊰]-general-cancellation e2))
    = prepend (p ([∧]-elimᵣ ([⊰]-general-cancellation e1)) ([∧]-elimᵣ ([⊰]-general-cancellation e2)))

  ps : ∀{x y}{l} → Pred(swap{x = x}{y = y}{l = l})
  ps {x} {y} {ml} {x₁ ⊰ y₁ ⊰ l₁} {x₂ ⊰ y₂ ⊰ l₂} e₁ e₂
    rewrite injective(f) (symmetry(_≡_) ([∧]-elimₗ ([⊰]-general-cancellation e₁)) 🝖 [∧]-elimₗ ([⊰]-general-cancellation ([∧]-elimᵣ ([⊰]-general-cancellation e₂))))
    rewrite injective(f) (symmetry(_≡_) ([∧]-elimₗ ([⊰]-general-cancellation ([∧]-elimᵣ ([⊰]-general-cancellation e₁)))) 🝖 [∧]-elimₗ ([⊰]-general-cancellation e₂))
    rewrite injective(map f) ⦃ map-injective ⦄ (symmetry(_≡_) ([∧]-elimᵣ ([⊰]-general-cancellation ([∧]-elimᵣ ([⊰]-general-cancellation e₁)))) 🝖 [∧]-elimᵣ ([⊰]-general-cancellation ([∧]-elimᵣ ([⊰]-general-cancellation e₂))))
    = swap

  pt : ∀{l₁ l₂ l₃}{p : l₁ permutes l₂}{q : l₂ permutes l₃} → Pred(p) → Pred(q) → Pred(trans p q)
  pt {fl₁} {fl₂} {fl₃} {p12}{p23} p1 p2 {l₁}{l₃} e1 e3 =
    let [∃]-intro l₂ ⦃ e2 ⦄ = map-existence {l₁}{fl₂} (trans (symmetry(_permutes_) (sub₂(_≡_)(_permutes_) e1)) p12)
    in trans{l₁ = l₁}{l₂ = l₂}{l₃ = l₃} (p1 e1 e2) (p2 e2 e3)
    where
      map-existence : ∀{l₁}{fl₂} → (map f(l₁) permutes fl₂) → ∃(l₂ ↦ fl₂ ≡ map f(l₂))
      map-existence{l₁}{fl₂} p = permutes-elim(\{mx my} (_ : mx permutes my) → ∀{x} → (mx ≡ map f(x)) → ∃(y ↦ my ≡ map f(y)))
        (\{ {∅} _ → [∃]-intro ∅ ⦃ [≡]-intro ⦄ })
        (\{ {fx}{fl₁}{fl₂}{p12} prev {x ⊰ l₁} e →
          let [∃]-intro l₂ ⦃ el₂ ⦄ = prev ([∧]-elimᵣ ([⊰]-general-cancellation e))
          in [∃]-intro (x ⊰ l₂) ⦃ congruence₂(_⊰_) ([∧]-elimₗ ([⊰]-general-cancellation e)) el₂ ⦄
        })
        (\{ {fx}{fy}{fl₁}{x ⊰ y ⊰ l₁} e → [∃]-intro (y ⊰ x ⊰ l₁) ⦃ congruence₂(_⊰_) ([∧]-elimₗ ([⊰]-general-cancellation ([∧]-elimᵣ ([⊰]-general-cancellation e)))) (congruence₂(_⊰_) ([∧]-elimₗ ([⊰]-general-cancellation e)) ([∧]-elimᵣ ([⊰]-general-cancellation ([∧]-elimᵣ ([⊰]-general-cancellation e))))) ⦄ })
        (\{fl₁}{fl₂}{fl₃}{p12}{p23} prev1 prev2 {l₁} e1 → prev2 ([∃]-proof (prev1 e1)))
        p
        [≡]-intro

  proof : Names.Injective ⦃ permutes-equiv ⦄ ⦃ permutes-equiv ⦄ (map f)
  proof p = permutes-elim Pred pe (\{x}{l₁}{l₂}{p} → pp{x}{l₁}{l₂}{p}) ps (\{l₁}{l₂}{l₃}{p}{q} → pt{l₁}{l₂}{l₃}{p}{q}) p [≡]-intro [≡]-intro

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

instance
  permutes-[≡]-subtransitivityₗ : Subtransitivityₗ(_permutes_ {T = T})(_≡_)
  permutes-[≡]-subtransitivityₗ = subrelation-transitivity-to-subtransitivityₗ
