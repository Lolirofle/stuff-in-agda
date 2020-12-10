module Numeral.Finite.Sequence where

import      Lvl
open import Data.Either as Either using (_‖_)
open import Data.Either.Proofs
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Functional
open import Function.Equals
open import Function.Equals.Proofs
import      Function.Names as Names
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
open import Structure.Operator
open import Structure.Relator
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
concat-left-pattern {a = 𝐒 a} {b} {af} {bf} {𝟎} {aa} p = [∃]-intro 𝟎 ⦃ injective(Either.Left) ⦃ Left-injective ⦄ p ⦄
concat-left-pattern {a = 𝐒 a} {𝟎} {af} {bf} {𝐒 n} {aa} p rewrite concat-is-left-on-0 {af = af}{bf = bf}{n = 𝐒 n} = [∃]-intro (𝐒(n)) ⦃ injective(Either.Left) ⦃ Left-injective ⦄ p ⦄
concat-left-pattern {a = 𝐒 a} {𝐒 b} {af} {bf} {𝐒 n} {aa} p with concat-left-pattern {a = a}{𝐒 b}{af ∘ 𝐒}{bf}{n}
... | q with q p
... | [∃]-intro witness ⦃ proof ⦄ = [∃]-intro (𝐒 witness) ⦃ proof ⦄

concat-right-pattern : ∀{a b}{af : 𝕟(a) → A}{bf : 𝕟(b) → B}{n : 𝕟(a ℕ.+ b)}{bb} → (concat af bf n ≡ Either.Right(bb)) → ∃(k ↦ (bf(k) ≡ bb))
concat-right-pattern {a = 𝟎} {𝟎}     {af} {bf} {}
concat-right-pattern {a = 𝟎} {𝐒 b}   {af} {bf} {𝟎} {bb} p = [∃]-intro 𝟎 ⦃ injective(Either.Right) ⦃ Right-injective ⦄ p ⦄
concat-right-pattern {a = 𝟎} {𝐒 b}   {af} {bf} {𝐒 n} {bb} p = [∃]-intro (𝐒(n)) ⦃ injective(Either.Right) ⦃ Right-injective ⦄ p ⦄
concat-right-pattern {a = 𝐒 a} {𝟎}   {af} {bf} {𝐒 n} {bb} p = concat-right-pattern {a = a}{𝟎} {af ∘ 𝐒}{bf} {n} {bb} p
concat-right-pattern {a = 𝐒 a} {𝐒 b} {af} {bf} {𝐒 n} {bb} p = concat-right-pattern {a = a}{𝐒 b}{af ∘ 𝐒}{bf}{n} p

concat-left-or-right : ∀{a b}{af : 𝕟(a) → A}{bf : 𝕟(b) → B}{n : 𝕟(a ℕ.+ b)} → ∃(aa ↦ concat af bf n ≡ Either.Left(af(aa))) ∨ ∃(bb ↦ concat af bf n ≡ Either.Right(bf(bb)))
concat-left-or-right {a = a} {b} {af} {bf} {n} with concat af bf n | inspect (concat af bf) n
... | [∨]-introₗ aa | intro q with [∃]-intro r ⦃ rp ⦄ ← concat-left-pattern{a = a}{b}{af}{bf}{n}{aa} q = [∨]-introₗ ([∃]-intro r ⦃ [≡]-with(Either.Left) (symmetry(_≡_) rp) ⦄)
... | [∨]-introᵣ bb | intro q with [∃]-intro r ⦃ rp ⦄ ← concat-right-pattern{a = a}{b}{af}{bf}{n}{bb} q = [∨]-introᵣ ([∃]-intro r ⦃ [≡]-with(Either.Right) (symmetry(_≡_) rp) ⦄)

instance
  concat-injective : ∀{a b}{af : 𝕟(a) → A}{bf : 𝕟(b) → B} → ⦃ Injective(af) ⦄ → ⦃ Injective(bf) ⦄ → Injective(concat af bf)
  Injective.proof (concat-injective {a = 𝟎} {𝐒 b} {af} {bf}) {x} {y} p = injective(bf) (injective(Either.Right) ⦃ Right-injective ⦄ p)
  Injective.proof (concat-injective {a = 𝐒 a} {b} {af} {bf}) {𝟎} {𝟎} p = [≡]-intro
  Injective.proof (concat-injective {a = 𝐒 a} {𝟎} {af} {bf}) {𝟎} {𝐒 y} p rewrite concat-is-left-on-0 {af = af}{bf = bf}{n = 𝐒 y} with () ← injective(af) (injective(Either.Left) ⦃ Left-injective ⦄ p)
  Injective.proof (concat-injective {a = 𝐒 a} {𝟎} {af} {bf}) {𝐒 x} {𝟎} p rewrite concat-is-left-on-0 {af = af}{bf = bf}{n = 𝐒 x} with () ← injective(af) (injective(Either.Left) ⦃ Left-injective ⦄ p)
  Injective.proof (concat-injective {a = 𝐒 a} {𝐒 b} {af} {bf}) {𝟎} {𝐒 y} p with concat-left-or-right{af = af ∘ 𝐒}{bf = bf}{n = y}
  ... | [∨]-introₗ ([∃]-intro _ ⦃ proof ⦄) with () ← injective(af) (injective(Either.Left) ⦃ Left-injective ⦄ (p 🝖 proof))
  ... | [∨]-introᵣ ([∃]-intro _ ⦃ proof ⦄) with () ← p 🝖 proof
  Injective.proof (concat-injective {a = 𝐒 a} {𝐒 b} {af} {bf}) {𝐒 x} {𝟎} p with concat-left-or-right{af = af ∘ 𝐒}{bf = bf}{n = x}
  ... | [∨]-introₗ ([∃]-intro _ ⦃ proof ⦄) with () ← injective(af) (injective(Either.Left) ⦃ Left-injective ⦄ (symmetry(_≡_) p 🝖 proof))
  ... | [∨]-introᵣ ([∃]-intro _ ⦃ proof ⦄) with () ← symmetry(_≡_) p 🝖 proof
  {-# CATCHALL #-}
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

module Interleaving where
  join : (𝕟(a) ‖ 𝕟(b)) → 𝕟(a ℕ.+ b)
  join {𝟎}  {𝐒 b} (Either.Right n)     = n
  join {𝐒 a}{𝟎}   (Either.Left  n)     = n
  join {𝐒 a}{𝐒 b} (Either.Left  𝟎)     = 𝟎
  join {𝐒 a}{𝐒 b} (Either.Right 𝟎)     = 𝐒(𝟎)
  join {𝐒 a}{𝐒 b} (Either.Left  (𝐒 n)) = 𝐒(𝐒(join {a}{b} (Either.Left n)))
  join {𝐒 a}{𝐒 b} (Either.Right (𝐒 n)) = 𝐒(𝐒(join {a}{b} (Either.Right n)))

  split : 𝕟(a ℕ.+ b) → (𝕟(a) ‖ 𝕟(b))
  split {𝟎}   {𝐒 b} n         = Either.Right n
  split {𝐒 a} {𝟎}   n         = Either.Left  n
  split {𝐒 a} {𝐒 b} 𝟎         = Either.Left  𝟎
  split {𝐒 a} {𝐒 b} (𝐒(𝟎))    = Either.Right 𝟎
  split {𝐒 a} {𝐒 b} (𝐒(𝐒(n))) = Either.map2 𝐒 𝐒 (split {a} {b} n)

  instance
    join-split-inverse : Inverseᵣ(join{a}{b})(split{a}{b})
    join-split-inverse {a}{b} = intro(proof{a}{b}) where
      proof : ∀{a b} → Names.Inverses(join{a}{b})(split{a}{b})
      proof {𝟎}  {𝐒 b}{𝟎}      = [≡]-intro
      proof {𝟎}  {𝐒 b}{𝐒 n}    = [≡]-intro
      proof {𝐒 a}{𝟎}  {𝟎}      = [≡]-intro
      proof {𝐒 a}{𝟎}  {𝐒 n}    = [≡]-intro
      proof {𝐒 a}{𝐒 b}{𝟎}      = [≡]-intro
      proof {𝐒 a}{𝐒 b}{𝐒 𝟎}    = [≡]-intro
      proof {𝐒 a}{𝐒 b}{𝐒(𝐒 n)} with split{a}{b} n | proof {a}{b}{n}
      ... | Either.Left  m | p = congruence₁(𝐒) (congruence₁(𝐒) p)
      ... | Either.Right m | p = congruence₁(𝐒) (congruence₁(𝐒) p)

  instance
    split-join-inverse : Inverseₗ(join{a}{b})(split{a}{b})
    split-join-inverse {a}{b} = intro(proof{a}{b}) where
      proof : ∀{a b} → Names.Inverses(split{a}{b})(join{a}{b})
      proof {𝟎}      {𝟎}      {Either.Left  ()}
      proof {𝟎}      {𝟎}      {Either.Right ()}
      proof {𝟎}      {𝐒 b}    {Either.Right n}     = [≡]-intro
      proof {𝐒 a}    {𝟎}      {Either.Left  n}     = [≡]-intro
      proof {𝐒 a}    {𝐒 b}    {Either.Left  𝟎}     = [≡]-intro
      proof {𝐒 a}    {𝐒 b}    {Either.Right 𝟎}     = [≡]-intro
      proof {𝐒(𝐒 a)} {𝐒 𝟎}    {Either.Left  (𝐒 n)} = [≡]-intro
      proof {𝐒 𝟎}    {𝐒(𝐒 b)} {Either.Right (𝐒 n)} = [≡]-intro
      proof {𝐒(𝐒 a)} {𝐒(𝐒 b)} {Either.Left  (𝐒 n)} with join{𝐒 a}{𝐒 b} (Either.Left n) | proof {𝐒 a}{𝐒 b}{Either.Left n}
      ... | 𝟎      | p = congruence₁(Either.map2 𝐒 𝐒) p
      ... | 𝐒(𝐒 m) | p = congruence₁(Either.map2 𝐒 𝐒) p
      proof {𝐒(𝐒 a)} {𝐒(𝐒 b)} {Either.Right (𝐒 n)} with join{𝐒 a}{𝐒 b} (Either.Right n) | proof {𝐒 a}{𝐒 b}{Either.Right n}
      ... | 𝐒(𝟎)   | p = congruence₁(Either.map2 𝐒 𝐒) p
      ... | 𝐒(𝐒 m) | p = congruence₁(Either.map2 𝐒 𝐒) p

interleave-join-equality : ∀{af : 𝕟(a) → A}{bf : 𝕟(b) → B} → (interleave af bf ∘ Interleaving.join ⊜ Either.map2 af bf)
interleave-join-equality {a = a}{b = b} = intro(p{a = a}{b = b}) where
  p : ∀{a b}{af : 𝕟(a) → A}{bf : 𝕟(b) → B} → (interleave af bf ∘ Interleaving.join Names.⊜ Either.map2 af bf)
  p {a = 𝟎}  {b = 𝐒 b} {af}{bf} {Either.Right n}     = [≡]-intro
  p {a = 𝐒 a}{b = 𝟎}   {af}{bf} {Either.Left  n}     = [≡]-intro
  p {a = 𝐒 a}{b = 𝐒 b} {af}{bf} {Either.Left  𝟎}     = [≡]-intro
  p {a = 𝐒 a}{b = 𝐒 b} {af}{bf} {Either.Right 𝟎}     = [≡]-intro
  p {a = 𝐒 a}{b = 𝐒 b} {af}{bf} {Either.Left  (𝐒 n)} = p {a = a}{b = b} {af ∘ 𝐒}{bf ∘ 𝐒} {Either.Left  n}
  p {a = 𝐒 a}{b = 𝐒 b} {af}{bf} {Either.Right (𝐒 n)} = p {a = a}{b = b} {af ∘ 𝐒}{bf ∘ 𝐒} {Either.Right n}

interleave-split-equality : ∀{af : 𝕟(a) → A}{bf : 𝕟(b) → B} → (interleave af bf ⊜ Either.map2 af bf ∘ Interleaving.split)
interleave-split-equality {a = a}{b = b}{af = af}{bf = bf} =
  interleave af bf                                                🝖[ _⊜_ ]-[]
  interleave af bf ∘ id                                           🝖[ _⊜_ ]-[ congruence₂ᵣ(_∘_)(interleave af bf) (intro(inverseᵣ(Interleaving.join{a}{b})(Interleaving.split{a}{b}))) ]-sym
  interleave af bf ∘ Interleaving.join{a}{b} ∘ Interleaving.split 🝖[ _⊜_ ]-[ congruence₂ₗ(_∘_)(Interleaving.split) (interleave-join-equality{a = a}{b = b}{af = af}{bf = bf}) ]
  Either.map2 af bf ∘ Interleaving.split                          🝖-end

instance
  interleave-injective : ∀{af : 𝕟(a) → A}{bf : 𝕟(b) → B} → ⦃ Injective(af) ⦄ → ⦃ Injective(bf) ⦄ → Injective(interleave af bf)
  interleave-injective {a = a}{b = b}{af = af}{bf = bf} = substitute₁ₗ(Injective) (interleave-split-equality {af = af}{bf = bf}) ([∘]-injective {f = Either.map2 af bf}{g = Interleaving.split} ⦃ inj-g = inverse-to-injective ⦃ inver = [∧]-intro Interleaving.join-split-inverse Interleaving.split-join-inverse ⦄ ⦄)

instance
  interleave-surjective : ∀{af : 𝕟(a) → A}{bf : 𝕟(b) → B} → ⦃ Surjective(af) ⦄ → ⦃ Surjective(bf) ⦄ → Surjective(interleave af bf)
  interleave-surjective {a = a}{b = b}{af = af}{bf = bf} = substitute₁ₗ(Surjective) (interleave-split-equality {af = af}{bf = bf}) ([∘]-surjective {f = Either.map2 af bf}{g = Interleaving.split} ⦃ surj-g = inverse-to-surjective ⦃ inver = [∧]-intro Interleaving.join-split-inverse Interleaving.split-join-inverse ⦄ ⦄)

instance
  interleave-bijective : ∀{af : 𝕟(a) → A}{bf : 𝕟(b) → B} → ⦃ Bijective(af) ⦄ → ⦃ Bijective(bf) ⦄ → Bijective(interleave af bf)
  interleave-bijective {a = a}{b = b}{af = af}{bf = bf} = substitute₁ₗ(Bijective) (interleave-split-equality {af = af}{bf = bf}) ([∘]-bijective {f = Either.map2 af bf}{g = Interleaving.split} ⦃ bij-g = inverse-to-bijective ⦃ inver = [∧]-intro Interleaving.join-split-inverse Interleaving.split-join-inverse ⦄ ⦄)

module Concatenation where
  join : (𝕟(a) ‖ 𝕟(b)) → 𝕟(a ℕ.+ b)
  join {a} {b} (Either.Left  n) = bound-[≤] [≤]-of-[+]ₗ n
  join {a} {b} (Either.Right n) = a 𝕟.Unclosed.+ₙₗ n

  split : 𝕟(a ℕ.+ b) → (𝕟(a) ‖ 𝕟(b))
  split {𝟎}  {𝐒 b} n     = Either.Right n
  split {𝐒 a}{𝟎}   n     = Either.Left n
  split {𝐒 a}{𝐒 b} 𝟎     = Either.Left 𝟎
  split {𝐒 a}{𝐒 b} (𝐒 n) = Either.mapLeft 𝐒 (split {a}{𝐒 b} n)

  open import Numeral.Finite.Category
  open import Numeral.Natural.Relation.Order
  open import Numeral.Natural.Relation.Order.Proofs
  open import Structure.Category.Functor
  instance
    join-split-inverse : Inverseᵣ(join{a}{b})(split{a}{b})
    join-split-inverse {a}{b} = intro(proof{a}{b}) where
      proof : ∀{a b} → Names.Inverses(join{a}{b})(split{a}{b})
      proof {𝟎}   {𝐒 b} {n} = [≡]-intro
      proof {𝐒 a} {𝟎}   {n} = _⊜_.proof (Functor.id-preserving bound-functor)
      proof {𝐒 a} {𝐒 b} {𝟎} = [≡]-intro
      proof {𝐒 a} {𝐒 b} {𝐒 n} with split {a}{𝐒 b} n | proof {a} {𝐒 b} {n}
      ... | Either.Left  _ | [≡]-intro = [≡]-intro
      ... | Either.Right _ | [≡]-intro = [≡]-intro

  instance
    split-join-inverse : Inverseₗ(join{a}{b})(split{a}{b})
    split-join-inverse {a}{b} = intro(proof{a}{b}) where
      proof : ∀{a b} → Names.Inverses(split{a}{b})(join{a}{b})
      proof {𝟎}   {𝐒 b} {Either.Right n}     = [≡]-intro
      proof {𝐒 a} {𝟎}   {Either.Left  n}     = congruence₁(Either.Left) (_⊜_.proof (Functor.id-preserving bound-functor))
      proof {𝐒 a} {𝐒 b} {Either.Left  𝟎}     = [≡]-intro
      proof {𝐒 a} {𝐒 b} {Either.Left  (𝐒 n)} = congruence₁(Either.mapLeft 𝐒) (proof{a}{𝐒 b} {Either.Left  n})
      proof {𝐒 a} {𝐒 b} {Either.Right n}     = congruence₁(Either.mapLeft 𝐒) (proof{a}{𝐒 b} {Either.Right n})

concat-split-equality : ∀{af : 𝕟(a) → A}{bf : 𝕟(b) → B} → (concat af bf ⊜ Either.map2 af bf ∘ Concatenation.split)
concat-split-equality {a = a}{b = b} = intro(p{a = a}{b = b}) where
  p : ∀{a b}{af : 𝕟(a) → A}{bf : 𝕟(b) → B} → (concat af bf Names.⊜ Either.map2 af bf ∘ Concatenation.split)
  p {a = 𝟎}     {b = 𝐒 b} {af = af}{bf = bf} {n}   = [≡]-intro
  p {a = 𝐒 a}   {b = 𝟎}   {af = af}{bf = bf} {𝟎}   = [≡]-intro
  p {a = 𝐒(𝐒 a)}{b = 𝟎}   {af = af}{bf = bf} {𝐒 n} = p{a = 𝐒 a}{b = 𝟎}{af = af ∘ 𝐒}{bf = bf}{n}
  p {a = 𝐒 a}   {b = 𝐒 b} {af = af}{bf = bf} {𝟎}   = [≡]-intro
  p {a = 𝐒 a}   {b = 𝐒 b} {af = af}{bf = bf} {𝐒 n} with Concatenation.split {a}{𝐒 b} n | p {a = a} {b = 𝐒 b} {af = af ∘ 𝐒} {bf = bf} {n}
  ... | Either.Left  _ | prev = prev
  ... | Either.Right _ | prev = prev

-- TODO: It is possible to copy-paste the proofs of inj/surj/bijectivity with a few modifications from Interleaving and apply it to Concatenation

module LinearSpaceFilling where
  join : (𝕟(a) ⨯ 𝕟(b)) → 𝕟(a ℕ.⋅ b)
  join = Tuple.uncurry(𝕟.Exact._⋅_)

  -- split : 𝕟(a ℕ.⋅ b) → (𝕟(a) ⨯ 𝕟(b))
  -- split {a}{b} n = ({!n mod a!} , {!n / a!})

module BaseNumerals where -- TODO: Maybe try to use Numeral.FixedPositional
  -- When interpreting the function as a numeral in a certain base, the parameters mean the following:
  -- • `a` is the base.
  -- • `b` is the length.
  -- • The argument of the specified function is the position of the numeral.
  -- • The value of the specified function is the digit on the argument's position.
  {-join : (𝕟(a) ← 𝕟(b)) → 𝕟(a ℕ.^ b)
  join {a}{𝟎}   f = 𝟎
  join {a}{𝐒 b} f = {!f(𝟎) 𝕟.Exact.+ ((join {a}{b} (f ∘ 𝐒)) 𝕟.Unclosed.⋅ₙᵣ a)!}-}
  -- f(𝟎) 𝕟.Exact.⋅ join {a}{b} (f ∘ 𝐒)
  -- 4321
  -- 1⋅10⁰ + 2⋅10¹ + 3⋅10² + 4⋅10³
  -- 1 + 10⋅(2 + 10⋅(3 + 10⋅(4 + 10⋅0)))

  -- TODO: Something is incorrect here. This is the type of the induction step:
  -- a + 𝐒(a⋅(a ^ b))
  -- 𝐒(a + a⋅(a ^ b))
  -- 𝐒(a + (a ^ 𝐒(b)))
  -- 𝐒(a) + (a ^ 𝐒(b))

  {-
  open import Data.Boolean
  join : (𝕟(a) → Bool) → 𝕟(2 ℕ.^ a)
  join {𝟎}   f = 𝟎
  join {𝐒 a} f = {!(if f(𝟎) then 𝕟.𝐒(𝕟.𝟎) else 𝕟.𝟎) 𝕟.Exact.+ join {a} (f ∘ 𝕟.𝐒)!}
  -}
