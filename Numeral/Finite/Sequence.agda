module Numeral.Finite.Sequence where

import      Lvl
open import Data.Either as Either using (_‖_)
open import Data.Either.Proofs
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Functional
open import Function.Proofs
open import Lang.Inspect
open import Lang.Instance
open import Logic
open import Logic.Predicate
open import Logic.Propositional
open import Numeral.Finite
open import Numeral.Finite.Bound
import      Numeral.Finite.Oper as 𝕟
open import Numeral.Finite.Proofs
open import Numeral.Natural
import      Numeral.Natural.Oper as ℕ
open import Numeral.Natural.Oper.Proofs
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Structure.Function
open import Structure.Function.Domain
open import Structure.Function.Domain.Proofs
open import Structure.Relator.Properties
open import Syntax.Transitivity
open import Type
open import Type.Size

private variable ℓ ℓ₁ ℓ₂ : Lvl.Level
private variable A : Type{ℓ₁}
private variable B : Type{ℓ₂}
private variable a b : ℕ

-- Interleaves two sequences into one, alternating between the elements and then putting the leftovers at the end.
interleave : (𝕟(a) → A) → (𝕟(b) → B) → (𝕟(a ℕ.+ b) → (A ‖ B))
interleave {a = 𝟎}   {b = 𝐒 b} af bf n        = Either.Right(bf(n))
interleave {a = 𝐒 a} {b = 𝟎}   af bf n        = Either.Left(af(n))
interleave {a = 𝐒 a} {b = 𝐒 b} af bf 𝟎        = Either.Left(af(𝟎))
interleave {a = 𝐒 a} {b = 𝐒 b} af bf (𝐒 𝟎)    = Either.Right(bf(𝟎))
interleave {a = 𝐒 a} {b = 𝐒 b} af bf (𝐒(𝐒 n)) = interleave {a = a}{b = b} (af ∘ 𝐒) (bf ∘ 𝐒) n

-- Concatenates two sequences into one, putting the elements of the first sequence first followed by the elements of the second sequence.
concat : (𝕟(a) → A) → (𝕟(b) → B) → (𝕟(a ℕ.+ b) → (A ‖ B))
concat {a = 𝟎}   {b = 𝐒 b} af bf n     = Either.Right(bf(n))
concat {a = 𝐒 a} {b = b}   af bf 𝟎     = Either.Left(af(𝟎))
concat {a = 𝐒 a} {b = b}   af bf (𝐒 n) = concat {a = a} {b = b} (af ∘ 𝐒) bf n



concat-is-left : ∀{a b}{af : 𝕟(a) → A}{bf : 𝕟(b) → B}{n : 𝕟(a)} → (concat af bf (bound-[+]ᵣ n) ≡ Either.Left(af(n)))
concat-is-left {a = 𝐒 a} {b = _} {n = 𝟎} = [≡]-intro
concat-is-left {a = 𝐒 a} {b = b} {n = 𝐒 n} = concat-is-left {a = a} {b = b} {n = n}

concat-is-left-on-0 : ∀{a}{af : 𝕟(a) → A}{bf : 𝕟(𝟎) → B}{n : 𝕟(a)} → (concat af bf n ≡ Either.Left(af(n)))
concat-is-left-on-0 {a = 𝐒 a} {n = 𝟎} = [≡]-intro
concat-is-left-on-0 {a = 𝐒 a} {n = 𝐒 n} = concat-is-left-on-0 {a = a} {n = n}
{-# REWRITE concat-is-left-on-0 #-}

-- concat-is-right : ∀{a b}{af : 𝕟(a) → A}{bf : 𝕟(𝐒 b) → B}{n : 𝕟(b)} → (concat af bf (maximum{n = a} 𝕟.+ n) ≡ Either.Right(bf(bound-𝐒 n)))

concat-left-pattern : ∀{a b}{af : 𝕟(a) → A}{bf : 𝕟(b) → B}{n : 𝕟(a ℕ.+ b)}{aa} → (concat af bf n ≡ Either.Left(aa)) → ∃(k ↦ (af(k) ≡ aa))
concat-left-pattern {a = 𝟎} {𝟎} {af} {bf} {()} {aa} p
concat-left-pattern {a = 𝐒 a} {b} {af} {bf} {𝟎} {aa} p = [∃]-intro 𝟎 ⦃ injective(Either.Left) p ⦄
concat-left-pattern {a = 𝐒 a} {𝟎} {af} {bf} {𝐒 n} {aa} p = [∃]-intro (𝐒(n)) ⦃ injective(Either.Left) p ⦄
concat-left-pattern {a = 𝐒 a} {𝐒 b} {af} {bf} {𝐒 n} {aa} p with concat-left-pattern {a = a}{𝐒 b}{af ∘ 𝐒}{bf}{n}
... | q with q p
... | [∃]-intro witness ⦃ proof ⦄ = [∃]-intro (𝐒 witness) ⦃ proof ⦄

concat-right-pattern : ∀{a b}{af : 𝕟(a) → A}{bf : 𝕟(b) → B}{n : 𝕟(a ℕ.+ b)}{bb} → (concat af bf n ≡ Either.Right(bb)) → ∃(k ↦ (bf(k) ≡ bb))
concat-right-pattern {a = 𝟎} {𝟎} {af} {bf} {()} {bb} p
concat-right-pattern {a = 𝟎} {𝐒 b} {af} {bf} {𝟎} {bb} p = [∃]-intro 𝟎 ⦃ injective(Either.Right) p ⦄
concat-right-pattern {a = 𝟎} {𝐒 b} {af} {bf} {𝐒 n} {bb} p = [∃]-intro (𝐒(n)) ⦃ injective(Either.Right) p ⦄
concat-right-pattern {a = 𝐒 a} {𝐒 b} {af} {bf} {𝐒 n} {bb} p with concat-right-pattern {a = a}{𝐒 b}{af ∘ 𝐒}{bf}{n}
... | q with q p
... | [∃]-intro witness ⦃ proof ⦄ = [∃]-intro (witness) ⦃ proof ⦄

concat-left-or-right : ∀{a b}{af : 𝕟(a) → A}{bf : 𝕟(b) → B}{n : 𝕟(a ℕ.+ b)} → ∃(aa ↦ concat af bf n ≡ Either.Left(af(aa))) ∨ ∃(bb ↦ concat af bf n ≡ Either.Right(bf(bb)))
concat-left-or-right {a = a} {b} {af} {bf} {n} with concat af bf n | inspect (concat af bf) n
... | [∨]-introₗ aa | intro q with [∃]-intro r ⦃ rp ⦄ ← concat-left-pattern{a = a}{b}{af}{bf}{n}{aa} q = [∨]-introₗ ([∃]-intro r ⦃ [≡]-with(Either.Left) (symmetry(_≡_) rp) ⦄)
... | [∨]-introᵣ bb | intro q with [∃]-intro r ⦃ rp ⦄ ← concat-right-pattern{a = a}{b}{af}{bf}{n}{bb} q = [∨]-introᵣ ([∃]-intro r ⦃ [≡]-with(Either.Right) (symmetry(_≡_) rp) ⦄)

instance
  concat-injective : ∀{a b}{af : 𝕟(a) → A}{bf : 𝕟(b) → B} → ⦃ Injective(af) ⦄ → ⦃ Injective(bf) ⦄ → Injective(concat af bf)
  Injective.proof (concat-injective {a = 𝟎} {𝐒 b} {af} {bf}) {x} {y} p = injective(bf) (injective(Either.Right) p)
  Injective.proof (concat-injective {a = 𝐒 a} {b} {af} {bf}) {𝟎} {𝟎} p = [≡]-intro
  Injective.proof (concat-injective {a = 𝐒 a} {𝟎} {af} {bf}) {𝟎} {𝐒 y} p with () ← injective(af) (injective(Either.Left) p)
  Injective.proof (concat-injective {a = 𝐒 a} {𝟎} {af} {bf}) {𝐒 x} {𝟎} p with () ← injective(af) (injective(Either.Left) p)
  Injective.proof (concat-injective {a = 𝐒 a} {𝐒 b} {af} {bf}) {𝟎} {𝐒 y} p with concat-left-or-right{af = af ∘ 𝐒}{bf = bf}{n = y}
  ... | [∨]-introₗ ([∃]-intro _ ⦃ proof ⦄) with () ← injective(af) (injective(Either.Left) (p 🝖 proof))
  ... | [∨]-introᵣ ([∃]-intro _ ⦃ proof ⦄) with () ← p 🝖 proof
  Injective.proof (concat-injective {a = 𝐒 a} {𝐒 b} {af} {bf}) {𝐒 x} {𝟎} p with concat-left-or-right{af = af ∘ 𝐒}{bf = bf}{n = x}
  ... | [∨]-introₗ ([∃]-intro _ ⦃ proof ⦄) with () ← injective(af) (injective(Either.Left) (symmetry(_≡_) p 🝖 proof))
  ... | [∨]-introᵣ ([∃]-intro _ ⦃ proof ⦄) with () ← symmetry(_≡_) p 🝖 proof
  Injective.proof (concat-injective {a = 𝐒 a} {b} {af} {bf}) {𝐒 x} {𝐒 y} p = congruence₁(𝐒) (Injective.proof (concat-injective {a = a} {b} {af ∘ 𝐒} {bf} ⦃ [∘]-injective {f = af}{g = 𝐒} ⦄) {x} {y} p)

instance
  postulate concat-inverseᵣ : ∀{a b}{af : 𝕟(a) → A}{bf : 𝕟(b) → B} → ⦃ ∃(Inverseᵣ(af)) ⦄ → ⦃ ∃(Inverseᵣ(bf)) ⦄ → ∃(Inverseᵣ(concat af bf))
{-  concat-inverseᵣ {A = A}{B = B} {a = a} {𝟎}   {af} {bf} ⦃ [∃]-intro af⁻¹ ⦃ af-inv ⦄ ⦄  ⦃ [∃]-intro bf⁻¹ ⦃ bf-inv ⦄ ⦄ = [∃]-intro concat⁻¹ ⦃ inv ⦄ where
    concat⁻¹ : (A ‖ B) → 𝕟(a)
    concat⁻¹ (Either.Left  aa) = af⁻¹(aa)
    concat⁻¹ (Either.Right bb) with () ← bf⁻¹(bb)

    inv : Inverseᵣ(concat af bf) concat⁻¹
    Inverseᵣ.proof inv {Either.Left  aa} = congruence₁ Either.Left (Inverseᵣ.proof af-inv {aa})
    Inverseᵣ.proof inv {Either.Right bb} with () ← bf⁻¹(bb)
  concat-inverseᵣ {A = A}{B = B} {a = a} {𝐒 b} {af} {bf} ⦃ [∃]-intro af⁻¹ ⦃ af-inv ⦄ ⦄  ⦃ [∃]-intro bf⁻¹ ⦃ bf-inv ⦄ ⦄ = [∃]-intro concat⁻¹ ⦃ inv ⦄ where
    concat⁻¹ : (A ‖ B) → 𝕟(a ℕ.+ 𝐒(b))
    concat⁻¹ (Either.Left  aa) = 𝕟._+_ {a}{𝐒(b)} (af⁻¹(aa)) maximum
    concat⁻¹ (Either.Right bb) = bound-[+]ₗ {a}{𝐒 b} (bf⁻¹(bb))

    inv : Inverseᵣ(concat af bf) concat⁻¹
    Inverseᵣ.proof inv {Either.Left  aa} = {!!}
    Inverseᵣ.proof inv {Either.Right bb} = {!!}
-}
instance
  postulate concat-surjective : ∀{a b}{af : 𝕟(a) → A}{bf : 𝕟(b) → B} → ⦃ Surjective(af) ⦄ → ⦃ Surjective(bf) ⦄ → Surjective(concat af bf)
  {-Surjective.proof (concat-surjective {a = 𝟎}  {b}   {af}{bf}) {Either.Left  y} with () ← [∃]-witness(surjective(af){y})
  Surjective.proof (concat-surjective {a = 𝟎}  {𝟎}   {af}{bf}) {Either.Right y} with () ← [∃]-witness(surjective(bf){y})
  Surjective.proof (concat-surjective {a = 𝐒 a}{𝟎}   {af}{bf}) {Either.Right y} with () ← [∃]-witness(surjective(bf){y})
  Surjective.proof (concat-surjective {a = 𝟎}  {𝐒 b} {af}{bf}) {Either.Right y} = [∃]-map-proof (congruence₁(Either.Right)) (surjective(bf))
  Surjective.proof (concat-surjective {a = 𝐒 a}{𝟎}   {af}{bf}) {Either.Left  y} = [∃]-map-proof (congruence₁(Either.Left)) (surjective(af))
  Surjective.proof (concat-surjective {a = 𝐒 a}{𝐒 b} {af}{bf}) {Either.Left  y} with surjective(af){y}
  ... | [∃]-intro 𝟎     ⦃ [≡]-intro ⦄ = [∃]-intro 𝟎 ⦃ [≡]-intro ⦄
  ... | [∃]-intro (𝐒 x) ⦃ [≡]-intro ⦄ with p ← Surjective.proof (concat-surjective {a = a}{𝐒 b} {af ∘ 𝐒}{bf} ⦃ {!!} ⦄) {Either.Left (af(𝐒 x))} = {!!} -- TODO: If proven like this, then A in this call essentially needs to be A∖{af(𝐒 x)} because (𝕟(a) → A) is not surjective when (𝕟(𝐒(a)) → A) is
  -- Surjective.proof (concat-surjective {a = {!a!}}{𝐒 b} {{!af ∘ 𝐒!}}{bf} ⦃ {!!} ⦄) {Either.Left  y}
  Surjective.proof (concat-surjective {a = 𝐒 a}{𝐒 b} {af}{bf}) {Either.Right y} = {!!}
-}
instance
  concat-bijective : ∀{a b}{af : 𝕟(a) → A}{bf : 𝕟(b) → B} → ⦃ Bijective(af) ⦄ → ⦃ Bijective(bf) ⦄ → Bijective(concat af bf)
  concat-bijective {af = af}{bf = bf} =
    injective-surjective-to-bijective(concat af bf)
      ⦃ concat-injective  ⦃ bijective-to-injective (af) ⦄ ⦃ bijective-to-injective (bf) ⦄ ⦄
      ⦃ concat-surjective ⦃ bijective-to-surjective(af) ⦄ ⦃ bijective-to-surjective(bf) ⦄ ⦄

instance
  postulate interleave-injective : ∀{a b}{af : 𝕟(a) → A} {bf : 𝕟(b) → B} ⦃ _ : Injective(af) ⦄ → ⦃ Injective(bf) ⦄ → Injective(interleave af bf)
  {-Injective.proof (interleave-injective {a = 𝟎}   {b = 𝐒 b} {af} {bf}) = injective(bf) ∘ injective(Either.Right)
  Injective.proof (interleave-injective {a = 𝐒 a} {b = 𝟎}   {af} {bf}) = injective(af) ∘ injective(Either.Left)
  Injective.proof (interleave-injective {a = 𝐒 a} {b = 𝐒 b} {af} {bf}) {𝟎}     {𝟎}      fxfy = [≡]-intro
  Injective.proof (interleave-injective {a = 𝐒 a} {b = 𝐒 b} {af} {bf}) {𝐒 𝟎}   {𝐒 𝟎}    fxfy = [≡]-intro
  Injective.proof (interleave-injective {a = 𝐒 a} {b = 𝐒 b} {af} {bf}) {𝟎}     {𝐒(𝐒 y)} fxfy = {!!}
  Injective.proof (interleave-injective {a = 𝐒 a} {b = 𝐒 b} {af} {bf}) {𝐒(𝐒 x)}{𝟎}      fxfy = {!!}
  Injective.proof (interleave-injective {a = 𝐒 a} {b = 𝐒 b} {af} {bf}) {𝐒 𝟎}   {𝐒(𝐒 y)} fxfy = congruence₁(𝐒) (Injective.proof (interleave-injective {a = 𝐒 a} {b = b} {af} {bf ∘ 𝐒} ⦃ infer ⦄ ⦃ [∘]-injective {f = bf} ⦄) {𝟎}     {𝐒 y} {!!})
  Injective.proof (interleave-injective {a = 𝐒 a} {b = 𝐒 b} {af} {bf}) {𝐒(𝐒 x)}{𝐒 𝟎}    fxfy = congruence₁(𝐒) (Injective.proof (interleave-injective {a = a} {b = 𝐒 b} {af ∘ 𝐒} {bf} ⦃ [∘]-injective {f = af} ⦄) {𝐒 x}     {𝟎} {!fxfy!})
  Injective.proof (interleave-injective {a = 𝐒 a} {b = 𝐒 b} {af} {bf}) {𝐒(𝐒 x)}{𝐒(𝐒 y)} fxfy = congruence₁(𝐒 ∘ 𝐒) (injective(interleave(af ∘ 𝐒)(bf ∘ 𝐒)) ⦃ interleave-injective {af = af ∘ 𝐒} {bf = bf ∘ 𝐒} ⦃ [∘]-injective {f = af} ⦄ ⦃ [∘]-injective {f = bf} ⦄ ⦄ fxfy)
  -}
