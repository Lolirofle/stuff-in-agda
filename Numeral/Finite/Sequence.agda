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
open import Numeral.Natural.Oper.Proofs.Order
open import Numeral.Natural.Relation.Order
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Structure.Function
open import Structure.Function.Domain
open import Structure.Function.Domain.Proofs
import      Structure.Function.Names as Names
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



concat-is-left : ∀{a b}{af : 𝕟(a) → A}{bf : 𝕟(b) → B}{n : 𝕟(a)} → (concat af bf (bound-[≤] [≤]-of-[+]ₗ n) ≡ Either.Left(af(n)))
concat-is-left {a = 𝐒 a} {b} {af}{bf} {n = 𝟎}   = [≡]-intro
concat-is-left {a = 𝐒 a} {𝟎} {af}{bf} {n = 𝐒 n} = ([≡]-with(concat af bf) (p{n = n})) 🝖 concat-is-left {a = a} {b = 𝟎} {af = af ∘ 𝐒}{bf = bf} {n = n} where
  p : ∀{A}{n : 𝕟(A)} → (bound-[≤] ([≤]-of-[+]ₗ {𝐒 A}{𝟎}) (𝐒(n)) ≡ 𝐒(bound-[≤] [≤]-of-[+]ₗ n))
  p {.(𝐒 _)} {𝟎}   = [≡]-intro
  p {.(𝐒 _)} {𝐒 n} = [≡]-intro
concat-is-left {a = 𝐒 a} {𝐒 b} {af}{bf} {n = 𝐒 n} = concat-is-left {a = a} {b = 𝐒 b} {af = af ∘ 𝐒}{bf = bf} {n = n}

concat-is-left-on-0 : ∀{a}{af : 𝕟(a) → A}{bf : 𝕟(𝟎) → B}{n : 𝕟(a)} → (concat af bf n ≡ Either.Left(af(n)))
concat-is-left-on-0 {a = 𝐒 a} {n = 𝟎} = [≡]-intro
concat-is-left-on-0 {a = 𝐒 a} {n = 𝐒 n} = concat-is-left-on-0 {a = a} {n = n}

-- concat-is-right : ∀{a b}{af : 𝕟(a) → A}{bf : 𝕟(𝐒 b) → B}{n : 𝕟(b)} → (concat af bf (maximum{n = a} 𝕟.+ n) ≡ Either.Right(bf(bound-𝐒 n)))

concat-left-pattern : ∀{a b}{af : 𝕟(a) → A}{bf : 𝕟(b) → B}{n : 𝕟(a ℕ.+ b)}{aa} → (concat af bf n ≡ Either.Left(aa)) → ∃(k ↦ (af(k) ≡ aa))
concat-left-pattern {a = 𝟎} {𝟎} {af} {bf} {}
concat-left-pattern {a = 𝐒 a} {b} {af} {bf} {𝟎} {aa} p = [∃]-intro 𝟎 ⦃ injective(Either.Left) p ⦄
concat-left-pattern {a = 𝐒 a} {𝟎} {af} {bf} {𝐒 n} {aa} p rewrite concat-is-left-on-0 {af = af}{bf = bf}{n = 𝐒 n} = [∃]-intro (𝐒(n)) ⦃ injective(Either.Left) p ⦄
concat-left-pattern {a = 𝐒 a} {𝐒 b} {af} {bf} {𝐒 n} {aa} p with concat-left-pattern {a = a}{𝐒 b}{af ∘ 𝐒}{bf}{n}
... | q with q p
... | [∃]-intro witness ⦃ proof ⦄ = [∃]-intro (𝐒 witness) ⦃ proof ⦄

concat-right-pattern : ∀{a b}{af : 𝕟(a) → A}{bf : 𝕟(b) → B}{n : 𝕟(a ℕ.+ b)}{bb} → (concat af bf n ≡ Either.Right(bb)) → ∃(k ↦ (bf(k) ≡ bb))
concat-right-pattern {a = 𝟎} {𝟎}     {af} {bf} {}
concat-right-pattern {a = 𝟎} {𝐒 b}   {af} {bf} {𝟎} {bb} p = [∃]-intro 𝟎 ⦃ injective(Either.Right) p ⦄
concat-right-pattern {a = 𝟎} {𝐒 b}   {af} {bf} {𝐒 n} {bb} p = [∃]-intro (𝐒(n)) ⦃ injective(Either.Right) p ⦄
concat-right-pattern {a = 𝐒 a} {𝟎}   {af} {bf} {𝐒 n} {bb} p = concat-right-pattern {a = a}{𝟎} {af ∘ 𝐒}{bf} {n} {bb} p
concat-right-pattern {a = 𝐒 a} {𝐒 b} {af} {bf} {𝐒 n} {bb} p = concat-right-pattern {a = a}{𝐒 b}{af ∘ 𝐒}{bf}{n} p

concat-left-or-right : ∀{a b}{af : 𝕟(a) → A}{bf : 𝕟(b) → B}{n : 𝕟(a ℕ.+ b)} → ∃(aa ↦ concat af bf n ≡ Either.Left(af(aa))) ∨ ∃(bb ↦ concat af bf n ≡ Either.Right(bf(bb)))
concat-left-or-right {a = a} {b} {af} {bf} {n} with concat af bf n | inspect (concat af bf) n
... | [∨]-introₗ aa | intro q with [∃]-intro r ⦃ rp ⦄ ← concat-left-pattern{a = a}{b}{af}{bf}{n}{aa} q = [∨]-introₗ ([∃]-intro r ⦃ [≡]-with(Either.Left) (symmetry(_≡_) rp) ⦄)
... | [∨]-introᵣ bb | intro q with [∃]-intro r ⦃ rp ⦄ ← concat-right-pattern{a = a}{b}{af}{bf}{n}{bb} q = [∨]-introᵣ ([∃]-intro r ⦃ [≡]-with(Either.Right) (symmetry(_≡_) rp) ⦄)

instance
  concat-injective : ∀{a b}{af : 𝕟(a) → A}{bf : 𝕟(b) → B} → ⦃ Injective(af) ⦄ → ⦃ Injective(bf) ⦄ → Injective(concat af bf)
  Injective.proof (concat-injective {a = 𝟎} {𝐒 b} {af} {bf}) {x} {y} p = injective(bf) (injective(Either.Right) p)
  Injective.proof (concat-injective {a = 𝐒 a} {b} {af} {bf}) {𝟎} {𝟎} p = [≡]-intro
  Injective.proof (concat-injective {a = 𝐒 a} {𝟎} {af} {bf}) {𝟎} {𝐒 y} p rewrite concat-is-left-on-0 {af = af}{bf = bf}{n = 𝐒 y} with () ← injective(af) (injective(Either.Left) p)
  Injective.proof (concat-injective {a = 𝐒 a} {𝟎} {af} {bf}) {𝐒 x} {𝟎} p rewrite concat-is-left-on-0 {af = af}{bf = bf}{n = 𝐒 x} with () ← injective(af) (injective(Either.Left) p)
  Injective.proof (concat-injective {a = 𝐒 a} {𝐒 b} {af} {bf}) {𝟎} {𝐒 y} p with concat-left-or-right{af = af ∘ 𝐒}{bf = bf}{n = y}
  ... | [∨]-introₗ ([∃]-intro _ ⦃ proof ⦄) with () ← injective(af) (injective(Either.Left) (p 🝖 proof))
  ... | [∨]-introᵣ ([∃]-intro _ ⦃ proof ⦄) with () ← p 🝖 proof
  Injective.proof (concat-injective {a = 𝐒 a} {𝐒 b} {af} {bf}) {𝐒 x} {𝟎} p with concat-left-or-right{af = af ∘ 𝐒}{bf = bf}{n = x}
  ... | [∨]-introₗ ([∃]-intro _ ⦃ proof ⦄) with () ← injective(af) (injective(Either.Left) (symmetry(_≡_) p 🝖 proof))
  ... | [∨]-introᵣ ([∃]-intro _ ⦃ proof ⦄) with () ← symmetry(_≡_) p 🝖 proof
  Injective.proof (concat-injective {a = 𝐒 a} {b} {af} {bf}) {𝐒 x} {𝐒 y} p = congruence₁(𝐒) (Injective.proof (concat-injective {a = a} {b} {af ∘ 𝐒} {bf} ⦃ [∘]-injective {f = af}{g = 𝐒} ⦄) {x} {y} p)

concat-when-left : ∀{a b}{af : 𝕟(a) → A}{bf : 𝕟(b) → B}{n} → ∃(aa ↦ concat af bf n ≡ Either.Left(aa)) ↔ (𝕟-to-ℕ(n) < a)
concat-when-left {a = a} {b} {af} {bf} {n} = [↔]-intro l r where
  l : ∀{a b}{af : 𝕟(a) → A}{bf : 𝕟(b) → B}{n} → ∃(aa ↦ concat af bf n ≡ Either.Left(aa)) ← (𝕟-to-ℕ(n) < a)
  l {a = .(𝐒 _)} {b} {af} {bf} {𝟎}   [≤]-with-[𝐒] = [∃]-intro (af(𝟎)) ⦃ reflexivity(_≡_) ⦄
  l {a = .(𝐒 _)} {b} {af} {bf} {𝐒 n} ([≤]-with-[𝐒] {y = a} ⦃ p ⦄) = l {a = a}{b}{af ∘ 𝐒}{bf}{n} p

  r : ∀{a b}{af : 𝕟(a) → A}{bf : 𝕟(b) → B}{n} → ∃(aa ↦ concat af bf n ≡ Either.Left(aa)) → (𝕟-to-ℕ(n) < a)
  r {a = 𝟎}   {b} {af} {bf} {𝟎}   ([∃]-intro aa ⦃ ⦄)
  r {a = 𝐒 a} {b} {af} {bf} {𝟎}   ([∃]-intro aa ⦃ p ⦄) = [<]-minimum
  r {a = 𝐒 a} {b} {af} {bf} {𝐒 n} ([∃]-intro aa ⦃ p ⦄) = [≤]-with-[𝐒] ⦃ r {a = a}{b}{af ∘ 𝐒}{bf}{n} ([∃]-intro aa ⦃ p ⦄) ⦄

concat-when-right : ∀{a b}{af : 𝕟(a) → A}{bf : 𝕟(b) → B}{n} → ∃(bb ↦ concat af bf n ≡ Either.Right(bb)) ↔ (a ≤ 𝕟-to-ℕ(n))
concat-when-right {a = a} {b} {af} {bf} {n} = [↔]-intro l r where
  l : ∀{a b}{af : 𝕟(a) → A}{bf : 𝕟(b) → B}{n} → ∃(bb ↦ concat af bf n ≡ Either.Right(bb)) ← (a ≤ 𝕟-to-ℕ(n))
  l {a = 𝟎}   {𝐒 b} {af} {bf} {n} [≤]-minimum  = [∃]-intro (bf(n)) ⦃ reflexivity(_≡_) ⦄
  l {a = 𝐒 a} {b} {af} {bf} {𝐒 n} ([≤]-with-[𝐒] ⦃ p ⦄) = l {a = a}{b}{af ∘ 𝐒}{bf}{n} p

  r : ∀{a b}{af : 𝕟(a) → A}{bf : 𝕟(b) → B}{n} → ∃(bb ↦ concat af bf n ≡ Either.Right(bb)) → (a ≤ 𝕟-to-ℕ(n))
  r {a = 𝟎}   {b} {af} {bf} {_}   ([∃]-intro bb ⦃ p ⦄) = [≤]-minimum
  r {a = 𝐒 a} {b} {af} {bf} {𝟎}   ([∃]-intro bb ⦃ ⦄)
  r {a = 𝐒 a} {b} {af} {bf} {𝐒 n} ([∃]-intro bb ⦃ p ⦄) = [≤]-with-[𝐒] ⦃ r {a = a}{b}{af ∘ 𝐒}{bf}{n} ([∃]-intro bb ⦃ p ⦄) ⦄

𝕟-shrink : ∀{A B} → (b : 𝕟(B)) → (𝕟-to-ℕ(b) < A) → 𝕟(A)
𝕟-shrink {𝐒 A}{𝐒 B} 𝟎     [≤]-with-[𝐒] = 𝟎
𝕟-shrink {𝐒 A}{𝐒 B} (𝐒 b) ([≤]-with-[𝐒] ⦃ p ⦄) = 𝐒(𝕟-shrink {A}{B} b p)

𝕟-subtract : ∀{A B} → (b : 𝕟(B)) → (A < 𝕟-to-ℕ(b)) → 𝕟(𝐒(A))
𝕟-subtract {𝟎}  {𝐒 B} (𝐒 b) [≤]-with-[𝐒] = 𝟎
𝕟-subtract {𝐒 A}{𝐒 B} (𝐒 b) ([≤]-with-[𝐒] ⦃ p ⦄) = 𝐒(𝕟-subtract {A}{B} b p)

concat-when-lesser : ∀{a b}{af : 𝕟(a) → A}{bf : 𝕟(b) → B}{n} → (na : 𝕟-to-ℕ(n) < a) → (concat af bf n ≡ Either.Left(af(𝕟-shrink n na)))
concat-when-lesser {a = 𝐒 a} {b} {af} {bf} {𝟎}   [≤]-with-[𝐒]         = [≡]-intro
concat-when-lesser {a = 𝐒 a} {b} {af} {bf} {𝐒 n} ([≤]-with-[𝐒] ⦃ p ⦄) = concat-when-lesser {a = a} {b} {af ∘ 𝐒} {bf} {n} p

{-
open import Numeral.Natural.Relation.Order.Proofs
concat-when-greater : ∀{a b}{af : 𝕟(a) → A}{bf : 𝕟(𝐒(b)) → B}{n} → (bn : 𝐒(b) < 𝕟-to-ℕ(n)) → (concat af bf n ≡ Either.Right(bf(𝕟-subtract n ([≤]-predecessor bn))))
concat-when-greater {a = 𝟎} {𝐒 b} {af} {bf} {𝐒 n} [≤]-with-[𝐒] = {!!}
concat-when-greater {a = 𝐒 a} {𝟎} {af} {bf} {𝐒 n} ([≤]-with-[𝐒] {y = y} ⦃ p ⦄) with n | 𝕟-to-ℕ n
... | 𝟎 | 𝟎 = {!concat-when-greater {a = a} {?} {af ∘ 𝐒} {bf} {𝟎}!}
... | 𝟎 | 𝐒 bb = {!!}
... | 𝐒 aa | 𝟎 = {!!}
... | 𝐒 aa | 𝐒 bb = {!!}
concat-when-greater {a = 𝐒 a} {𝐒 b} {af} {bf} {𝐒 n} ([≤]-with-[𝐒] {y = _} ⦃ p ⦄) = {!concat-when-greater {a = a} {𝐒 b} {af ∘ 𝐒} {bf} {n}!}

open import Numeral.Natural.Relation.Order.Proofs
bound-[≤]-of-refl : ∀{n}{x} → (bound-[≤] (reflexivity(_≤_) {n}) x ≡ x)
bound-[≤]-of-refl {𝐒 n} {𝟎}   = [≡]-intro
bound-[≤]-of-refl {𝐒 n} {𝐒 x} = [≡]-with(𝐒) (bound-[≤]-of-refl {n}{x})

concat-surjective-left : ∀{a b}{af : 𝕟(a) → A}{bf : 𝕟(b) → B}{x} → ⦃ Surjective(af) ⦄ → ∃(n ↦ concat af bf n ≡ Either.Left(x))
concat-surjective-left {a = 𝟎} {b} {af} {bf} {x} with () ← [∃]-witness(surjective(af) {x})
concat-surjective-left {a = 𝐒 a} {b} {af} {bf} {x} with [∃]-intro x ⦃ q ⦄ ← [↔]-to-[←] (concat-when-left {a = 𝐒 a}{b}{af}{bf}{{!!}}) {!!} = {!!}
{-∃.witness (concat-surjective-left {a = a} {b} {af} {bf} {x}) = bound-[≤] ([≤]-of-[+]ₗ {y = b}) ([∃]-witness(surjective(af) {x}))
∃.proof   (concat-surjective-left {a = 𝟎}   {_}   {af} {bf} {x}) with () ← [∃]-witness(surjective(af) {x})
∃.proof   (concat-surjective-left {a = 𝐒 a} {𝟎}   {af} {bf} {x}) rewrite bound-[≤]-of-refl {𝐒 a}{[∃]-witness(surjective(af) {x})} with surjective(af) {x}
... | [∃]-intro 𝟎     ⦃ p ⦄ = congruence₁(Either.Left) p
... | [∃]-intro (𝐒 c) ⦃ p ⦄ with [∃]-intro x ⦃ q ⦄ ← [↔]-to-[←] (concat-when-left {a = 𝐒 a}{𝟎}{af}{bf}{𝐒 c}) {!!} = {!!}
∃.proof   (concat-surjective-left {a = 𝐒 a} {𝐒 b} {af} {bf} {x}) = {!!}-}
-}

-- TODO: Something is incorrect about this
concat⁻¹ : (A → 𝕟(a)) → (B → 𝕟(b)) → ((A ‖ B) → 𝕟(a ℕ.+ b))
concat⁻¹ {a = 𝟎}   {b = _}   af⁻¹ bf⁻¹ ([∨]-introₗ x) with () ← af⁻¹(x)
concat⁻¹ {a = _}   {b = 𝟎}   af⁻¹ bf⁻¹ ([∨]-introᵣ x) with () ← bf⁻¹(x)
concat⁻¹ {a = 𝟎}   {b = 𝐒 b} af⁻¹ bf⁻¹ ([∨]-introᵣ x) = bf⁻¹(x)
concat⁻¹ {a = 𝐒 a} {b = 𝟎}   af⁻¹ bf⁻¹ ([∨]-introₗ x) = af⁻¹(x)
concat⁻¹ {a = 𝐒 a} {b = 𝐒 b} af⁻¹ bf⁻¹ ([∨]-introₗ x) = bound-[≤] ([≤]-of-[+]ₗ {y = 𝐒 b}) (af⁻¹(x))
concat⁻¹ {a = 𝐒 a} {b = 𝐒 b} af⁻¹ bf⁻¹ ([∨]-introᵣ x) = maximum{a} 𝕟.Exact.+ (bf⁻¹(x))

{- TODO: Recursion step is problematic
concat-inverseᵣ-step : ∀{a b}{af : 𝕟(𝐒(𝐒 a)) → A}{bf : 𝕟(b) → B}{af⁻¹ : A → 𝕟(𝐒(𝐒 a))}{bf⁻¹ : B → 𝕟(b)} → Names.Inverses(af)(af⁻¹) → Names.Inverses(af ∘ 𝐒)(𝕟.Exact.𝐏₀ ∘ af⁻¹)
concat-inverseᵣ-step {a = a} {b} {af} {bf} {af⁻¹} {bf⁻¹} p {x} with af⁻¹(x) | p{x}
... | 𝟎    | px = {!!}
... | 𝐒(y) | px = px
{-  (af ∘ 𝐒) ((𝕟.Exact.𝐏₀ ∘ af⁻¹) x) 🝖[ _≡_ ]-[]
  af(𝐒(𝕟.Exact.𝐏₀(af⁻¹(x))))       🝖[ _≡_ ]-[ {!!} ]
  af(af⁻¹(x))                      🝖[ _≡_ ]-[ {!!} ]
  x                                🝖-end
-}
concat-inverseᵣ : ∀{a b}{af : 𝕟(a) → A}{bf : 𝕟(b) → B}{af⁻¹}{bf⁻¹} → ⦃ Inverseᵣ(af)(af⁻¹) ⦄ → ⦃ Inverseᵣ(bf)(bf⁻¹) ⦄ → Inverseᵣ(concat af bf)(concat⁻¹ af⁻¹ bf⁻¹)
concat-inverseᵣ {af = af}{bf = bf} ⦃ intro pa ⦄ ⦃ intro pb ⦄ = intro(proof{af = af}{bf = bf} pa pb) where
  proof : ∀{a b}{af : 𝕟(a) → A}{bf : 𝕟(b) → B}{af⁻¹ : A → 𝕟(a)}{bf⁻¹ : B → 𝕟(b)} → Names.Inverses af af⁻¹ → Names.Inverses bf bf⁻¹ → Names.Inverses (concat af bf) (concat⁻¹ af⁻¹ bf⁻¹)
  proof {a = 𝟎}   {_}   {af} {bf} {af⁻¹} {bf⁻¹} pa pb {Either.Left  x} with () ← af⁻¹(x)
  proof {a = 𝟎}   {𝐒 b} {af} {bf} {af⁻¹} {bf⁻¹} pa pb {Either.Right x} =
    concat af bf (concat⁻¹ af⁻¹ bf⁻¹ (Either.Right x)) 🝖[ _≡_ ]-[]
    Either.Right (bf (bf⁻¹ x))                         🝖[ _≡_ ]-[ congruence₁(Either.Right) pb ]
    Either.Right x                                     🝖-end
  proof {a = _}   {𝟎}   {af} {bf} {af⁻¹} {bf⁻¹} pa pb {Either.Right x} with () ← bf⁻¹(x)
  proof {a = 𝐒 a} {𝟎}   {af} {bf} {af⁻¹} {bf⁻¹} pa pb {Either.Left  x} with af⁻¹ x | pa{x}
  ... | 𝟎 | ppa =
    concat af bf 𝟎     🝖[ _≡_ ]-[]
    Either.Left (af 𝟎) 🝖[ _≡_ ]-[ congruence₁(Either.Left) ppa ]
    Either.Left x      🝖-end
  ... | 𝐒 𝟎 | ppa =
    concat af bf (𝐒 𝟎)   🝖[ _≡_ ]-[]
    concat (af ∘ 𝐒) bf 𝟎 🝖[ _≡_ ]-[ {!!} ]
    concat (af ∘ 𝐒) bf (concat⁻¹ (𝕟.Exact.𝐏₀ ∘ af⁻¹) bf⁻¹ (Either.Left x)) 🝖[ _≡_ ]-[ proof{af = af ∘ 𝐒}{bf}{𝕟.Exact.𝐏₀ ∘ af⁻¹}{bf⁻¹} {!ppa!} pb {Either.Left x} ]
    Either.Left x        🝖-end
  ... | 𝐒(𝐒 y) | ppa =
    concat af bf (𝐒(𝐒 y))   🝖[ _≡_ ]-[]
    concat (af ∘ 𝐒) bf (𝐒 y) 🝖[ _≡_ ]-[ {!!} ]
    concat (af ∘ 𝐒) bf (concat⁻¹ (𝕟.Exact.𝐏₀ ∘ af⁻¹) bf⁻¹ (Either.Left x)) 🝖[ _≡_ ]-[ proof{af = af ∘ 𝐒}{bf}{𝕟.Exact.𝐏₀ ∘ af⁻¹}{bf⁻¹} {!ppa!} pb {Either.Left x} ]
    Either.Left x        🝖-end
{-    concat af bf (concat⁻¹ af⁻¹ bf⁻¹ (Either.Left x)) 🝖[ _≡_ ]-[]
    concat af bf (af⁻¹ x)                             🝖[ _≡_ ]-[ {!!} ]
    Either.Left (af (af⁻¹ x))                         🝖[ _≡_ ]-[ congruence₁(Either.Left) pa ]
    Either.Left x                                     🝖-end-}
  proof {a = 𝐒 a} {𝐒 b} {af} {bf} {af⁻¹} {bf⁻¹} pa pb {Either.Left  x} with af⁻¹ x | pa{x}
  ... | 𝟎   | ppa = congruence₁(Either.Left) ppa
  ... | 𝐒 y | ppa =
    concat af bf (bound-[≤] ([≤]-with-[𝐒] ⦃ [≤]-of-[+]ₗ ⦄) (𝐒 y)) 🝖[ _≡_ ]-[]
    concat (af ∘ 𝐒) bf (bound-[≤] [≤]-of-[+]ₗ y)                  🝖[ _≡_ ]-[ {!!} ]
    Either.Left x                                                 🝖-end
    {-concat af bf (concat⁻¹ af⁻¹ bf⁻¹ (Either.Left x))                 🝖[ _≡_ ]-[]
    concat af bf (bound-[≤] ([≤]-with-[𝐒] ⦃ [≤]-of-[+]ₗ ⦄) (af⁻¹(x))) 🝖[ _≡_ ]-[ {!!} ]
    Either.Left x                                                     🝖-end-}
  proof {a = 𝐒 𝟎}    {𝐒 b} {af} {bf} {af⁻¹} {bf⁻¹} pa pb {Either.Right x} =
    concat af bf (concat⁻¹ af⁻¹ bf⁻¹ (Either.Right x)) 🝖[ _≡_ ]-[]
    concat af bf (𝟎 𝕟.Exact.+ bf⁻¹(x))                 🝖[ _≡_ ]-[ {!!} ]
    -- concat af bf (bf⁻¹(x))                             🝖[ _≡_ ]-[ {!!} ]
    Either.Right x                                     🝖-end
  proof {a = 𝐒(𝐒 a)} {𝐒 b} {af} {bf} {af⁻¹} {bf⁻¹} pa pb {Either.Right x} =
    concat af bf (concat⁻¹ af⁻¹ bf⁻¹ (Either.Right x)) 🝖[ _≡_ ]-[]
    concat af bf (maximum{𝐒 a} 𝕟.Exact.+ bf⁻¹(x))      🝖[ _≡_ ]-[]
    concat (af ∘ 𝐒) bf (maximum{a} 𝕟.Exact.+ bf⁻¹(x))  🝖[ _≡_ ]-[ proof {a = 𝐒 a}{𝐒 b} {af ∘ 𝐒}{bf}{{!!}}{bf⁻¹} {!!} pb {Either.Right x} ]
    Either.Right x                                     🝖-end
-}

{-
instance
  concat-inverseᵣ : ∀{a b}{af : 𝕟(a) → A}{bf : 𝕟(b) → B} → ⦃ ∃(Inverseᵣ(af)) ⦄ → ⦃ ∃(Inverseᵣ(bf)) ⦄ → ∃(Inverseᵣ(concat af bf))
  concat-inverseᵣ {A = A} {B = B} {a = 𝐒 a} {b = 𝟎} {af} {bf} ⦃ [∃]-intro af⁻¹ ⦃ af-inv ⦄ ⦄ ⦃ [∃]-intro bf⁻¹ ⦃ bf-inv ⦄ ⦄ = [∃]-intro concat⁻¹ ⦃ inv ⦄ where
    concat⁻¹ : (A ‖ B) → 𝕟(𝐒 a)
    concat⁻¹ (Either.Left  aa) = af⁻¹(aa)
    concat⁻¹ (Either.Right bb) with () ← bf⁻¹(bb)

    inv : Inverseᵣ(concat af bf) concat⁻¹
    Inverseᵣ.proof inv {Either.Left  aa} with af⁻¹(aa) | inverseᵣ(af)(af⁻¹) ⦃ af-inv ⦄ {aa}
    ... | 𝟎 | p =
      concat af bf 𝟎     🝖[ _≡_ ]-[]
      Either.Left (af 𝟎) 🝖[ _≡_ ]-[ [≡]-with(Either.Left) p ]
      Either.Left aa     🝖-end
    ... | 𝐒 aa⁻¹ | p =
      concat af bf (𝐒 aa⁻¹)       🝖[ _≡_ ]-[]
      concat (af ∘ 𝐒) bf aa⁻¹     🝖[ _≡_ ]-[ {!inverseᵣ _ _ inv!} ]
      Either.Left((af ∘ 𝐒)(aa⁻¹)) 🝖[ _≡_ ]-[ [≡]-with(Either.Left) p ]
      Either.Left aa              🝖-end
    Inverseᵣ.proof inv {Either.Right bb} with () ← bf⁻¹(bb)
-}

  {-concat-inverseᵣ {A = A}{B = B} {a = a} {𝟎}   {af} {bf} ⦃ [∃]-intro af⁻¹ ⦃ af-inv ⦄ ⦄  ⦃ [∃]-intro bf⁻¹ ⦃ bf-inv ⦄ ⦄ = [∃]-intro concat⁻¹ ⦃ inv ⦄ where
    concat⁻¹ : (A ‖ B) → 𝕟(a)
    concat⁻¹ (Either.Left  aa) = af⁻¹(aa)
    concat⁻¹ (Either.Right bb) with () ← bf⁻¹(bb)

    inv : Inverseᵣ(concat af bf) concat⁻¹
    Inverseᵣ.proof inv {Either.Left  aa} =
      concat af bf (concat⁻¹ ([∨]-introₗ aa)) 🝖[ _≡_ ]-[]
      concat af bf (af⁻¹(aa))                 🝖[ _≡_ ]-[ {!!} ]
      [∨]-introₗ aa                           🝖-end
    -- congruence₁ Either.Left (Inverseᵣ.proof af-inv {aa})
    Inverseᵣ.proof inv {Either.Right bb} with () ← bf⁻¹(bb)
  concat-inverseᵣ {A = A}{B = B} {a = a} {𝐒 b} {af} {bf} ⦃ [∃]-intro af⁻¹ ⦃ af-inv ⦄ ⦄  ⦃ [∃]-intro bf⁻¹ ⦃ bf-inv ⦄ ⦄ = [∃]-intro concat⁻¹ ⦃ inv ⦄ where
    concat⁻¹ : (A ‖ B) → 𝕟(a ℕ.+ 𝐒(b))
    concat⁻¹ (Either.Left  aa) = 𝕟.Exact._+_ {a}{𝐒(b)} (af⁻¹(aa)) maximum
    concat⁻¹ (Either.Right bb) = bound-[≤] ([≤]-of-[+]ᵣ {a}{𝐒 b}) (bf⁻¹(bb))

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
