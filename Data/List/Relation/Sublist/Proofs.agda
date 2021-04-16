import      Lvl
open import Type

module Data.List.Relation.Sublist.Proofs {ℓ} {T : Type{ℓ}} where

open import Data.Boolean
import      Data.Either as Either
open import Data.List as List
open import Data.List.Functions as List hiding (skip)
open import Data.List.Proofs
open import Data.List.Relation.Sublist
open import Data.Tuple as Tuple using (_,_)
open import Functional
open import Logic.Propositional
open import Logic.Predicate
open import Numeral.Natural
open import Numeral.Natural.Inductions
open import Numeral.Natural.Relation.Order
open import Numeral.Natural.Relation.Order.Proofs
open import Relator.Equals
open import Relator.Equals.Proofs
open import Structure.Relator.Ordering
open import Structure.Relator.Ordering.Proofs
open import Structure.Relator.Properties

private variable ℓ₂ : Lvl.Level
private variable T₂ : Type{ℓ₂}
private variable a x y : T
private variable l l₁ l₂ l₃ : List(T)
private variable n : ℕ

[⊑]-reflexivity : (l ⊑ l)
[⊑]-reflexivity {∅}     = empty
[⊑]-reflexivity {a ⊰ l} = use([⊑]-reflexivity{l})

[⊑]-prepend : (l ⊑ x ⊰ l)
[⊑]-prepend {∅}     = skip empty
[⊑]-prepend {x ⊰ l} = skip [⊑]-reflexivity

[⊑]-without-[⊰] : ((x ⊰ l₁) ⊑ (y ⊰ l₂)) → (l₁ ⊑ l₂)
[⊑]-without-[⊰]                (use p)        = p
[⊑]-without-[⊰]                (skip(use p))  = skip p
[⊑]-without-[⊰] {x = x}{y = y} (skip(skip p)) = skip([⊑]-without-[⊰] {x = x}{y = y} (skip p))

[⊑]-transitivity : (l₁ ⊑ l₂) → (l₂ ⊑ l₃) → (l₁ ⊑ l₃)
[⊑]-transitivity empty       empty       = empty
[⊑]-transitivity empty       (skip l₂l₃) = skip l₂l₃
[⊑]-transitivity (use l₁l₂)  (use l₂l₃)  = use([⊑]-transitivity l₁l₂ l₂l₃)
[⊑]-transitivity (use l₁l₂)  (skip l₂l₃) = skip([⊑]-transitivity (use l₁l₂) l₂l₃)
[⊑]-transitivity (skip l₁l₂) (use l₂l₃)  = skip([⊑]-transitivity l₁l₂ l₂l₃)
[⊑]-transitivity (skip l₁l₂) (skip l₂l₃) = skip([⊑]-transitivity (skip l₁l₂) l₂l₃)

[⊑]-not-prepend : ¬((x ⊰ l) ⊑ l)
[⊑]-not-prepend {x} {x ⊰ l₂} (use  p) = [⊑]-not-prepend {x}{l₂} p
[⊑]-not-prepend {x} {y ⊰ _}  (skip p) = [⊑]-not-prepend([⊑]-without-[⊰] {y = y} (skip p))

[⊑]-antisymmetry : (l₂ ⊑ l₁) → (l₁ ⊑ l₂) → (l₁ ≡ l₂)
[⊑]-antisymmetry {∅}      {∅}       l        r        = [≡]-intro
[⊑]-antisymmetry {y ⊰ l₂} {.y ⊰ l₁} (use l)  r        = [≡]-with(y ⊰_) ([⊑]-antisymmetry l ([⊑]-without-[⊰] r))
[⊑]-antisymmetry {y ⊰ l₂} {.y ⊰ l₁} (skip l) (use r)  = [≡]-with(y ⊰_) ([⊑]-antisymmetry ([⊑]-without-[⊰] {y = y} (skip l)) r)
[⊑]-antisymmetry {y ⊰ l₂} {x ⊰ l₁}  (skip l) (skip r) = [⊥]-elim ([⊑]-not-prepend ([⊑]-transitivity (skip r) l))

[⊑]-minimum : (∅ ⊑ l)
[⊑]-minimum {∅}     = empty
[⊑]-minimum {a ⊰ l} = skip([⊑]-minimum{l})

[⊑]ᵣ-of-[++]ₗ : (l₁ ⊑ (l₂ ++ l₁))
[⊑]ᵣ-of-[++]ₗ {l₁}{∅}      = [⊑]-reflexivity
[⊑]ᵣ-of-[++]ₗ {l₁}{a ⊰ l₂} = skip{x = a}([⊑]ᵣ-of-[++]ₗ {l₁}{l₂})

[⊑]ᵣ-of-[++]ᵣ : (l₁ ⊑ (l₁ ++ l₂))
[⊑]ᵣ-of-[++]ᵣ {∅}     {l₂} = [⊑]-minimum
[⊑]ᵣ-of-[++]ᵣ {a ⊰ l₁}{l₂} = use([⊑]ᵣ-of-[++]ᵣ{l₁}{l₂})

[⊑]-tail : (tail l ⊑ l)
[⊑]-tail {∅}     = empty
[⊑]-tail {a ⊰ l} = skip [⊑]-reflexivity

[⊑]-map : ∀{f : T → T₂} → (l₁ ⊑ l₂) → (map f(l₁) ⊑ map f(l₂))
[⊑]-map empty    = empty
[⊑]-map (use  p) = use  ([⊑]-map p)
[⊑]-map (skip p) = skip ([⊑]-map p)

[⊑]-filter : ∀{f} → (filter f(l) ⊑ l)
[⊑]-filter {∅}         = empty
[⊑]-filter {x ⊰ l} {f} with f(x)
... | 𝑇 = use  ([⊑]-filter {l})
... | 𝐹 = skip ([⊑]-filter {l})

[⊑]-separate₂ : let (l₁ , l₂) = separate₂(l) in (l₁ ⊑ l) ∧ (l₂ ⊑ l)
Tuple.left  ([⊑]-separate₂ {∅})         = empty
Tuple.left  ([⊑]-separate₂ {x ⊰ ∅})     = [⊑]-reflexivity
Tuple.left  ([⊑]-separate₂ {x ⊰ y ⊰ l}) = use (skip (Tuple.left [⊑]-separate₂))
Tuple.right ([⊑]-separate₂ {∅})         = empty
Tuple.right ([⊑]-separate₂ {x ⊰ ∅})     = skip [⊑]-reflexivity
Tuple.right ([⊑]-separate₂ {x ⊰ y ⊰ l}) = skip (use (Tuple.right [⊑]-separate₂))

[⊑]-postpend : (l ⊑ postpend a l)
[⊑]-postpend {∅}     = skip empty
[⊑]-postpend {x ⊰ l} = use [⊑]-postpend

[⊑]-withoutIndex : (withoutIndex n l ⊑ l)
[⊑]-withoutIndex {𝟎}   {∅}     = empty
[⊑]-withoutIndex {𝐒 n} {∅}     = empty
[⊑]-withoutIndex {𝟎}   {x ⊰ l} = skip [⊑]-reflexivity
[⊑]-withoutIndex {𝐒 n} {x ⊰ l} = use [⊑]-withoutIndex

[⊑]-initial : (initial n l ⊑ l)
[⊑]-initial {𝟎}   {∅}     = empty
[⊑]-initial {𝐒 n} {∅}     = empty
[⊑]-initial {𝟎}   {x ⊰ l} = [⊑]-minimum
[⊑]-initial {𝐒 n} {x ⊰ l} = use [⊑]-initial

[⊑]-skip : (List.skip n l ⊑ l)
[⊑]-skip {𝟎}   {∅}     = empty
[⊑]-skip {𝐒 n} {∅}     = empty
[⊑]-skip {𝟎}   {x ⊰ l} = [⊑]-reflexivity
[⊑]-skip {𝐒 n} {x ⊰ l} = skip [⊑]-skip

[⊑]-empty : (l ⊑ ∅) → (l ≡ ∅)
[⊑]-empty {∅}     _ = [≡]-intro
[⊑]-empty {_ ⊰ _} ()

[⊑]-length : (l₁ ⊑ l₂) → (length(l₁) ≤ length(l₂))
[⊑]-length empty    = [≤]-minimum
[⊑]-length (use  p) = [≤]-with-[𝐒] ⦃ [⊑]-length p ⦄
[⊑]-length (skip p) = [≤]-predecessor ([≤]-with-[𝐒] ⦃ [⊑]-length p ⦄)



[⊏]-without-[⊰] : ((x ⊰ l₁) ⊏ (y ⊰ l₂)) → (l₁ ⊏ l₂)
[⊏]-without-[⊰]                (use p)         = p
[⊏]-without-[⊰]                (skip (use p))  = skip p
[⊏]-without-[⊰] {x = x}{y = y} (skip (skip p)) = skip ([⊑]-without-[⊰] {x = x}{y = y} (skip p))

[⊏]-irreflexivity : ¬(l ⊏ l)
[⊏]-irreflexivity {∅} ()
[⊏]-irreflexivity {x ⊰ l} p = [⊏]-irreflexivity {l} ([⊏]-without-[⊰] p)

[⊏]-to-[⊑] : (l₁ ⊏ l₂) → (l₁ ⊑ l₂)
[⊏]-to-[⊑] (use  p) = use ([⊏]-to-[⊑] p)
[⊏]-to-[⊑] (skip p) = skip p

[⊏]-skip-[⊰] : (l₁ ⊏ l₂) → (l₁ ⊏ (x ⊰ l₂))
[⊏]-skip-[⊰] (use p) = skip ([⊏]-to-[⊑] (use p))
[⊏]-skip-[⊰] (skip x) = skip (skip x)

[⊏]-transitivity : (l₁ ⊏ l₂) → (l₂ ⊏ l₃) → (l₁ ⊏ l₃)
[⊏]-transitivity p        (skip (skip q)) = skip(skip([⊑]-transitivity ([⊏]-to-[⊑] p) q))
[⊏]-transitivity (use p)  (use q)         = use ([⊏]-transitivity p q)
[⊏]-transitivity (use p)  (skip (use q))  = skip (use ([⊑]-transitivity ([⊏]-to-[⊑] p) q))
[⊏]-transitivity (skip p) (use q)         = skip([⊑]-transitivity p ([⊏]-to-[⊑] q))
[⊏]-transitivity (skip p) (skip (use q))  = skip(skip([⊑]-transitivity p q))

[⊏]-asymmetry : (l₂ ⊏ l₁) → (l₁ ⊏ l₂) → ⊥
[⊏]-asymmetry p q = [⊏]-irreflexivity([⊏]-transitivity p q)

[⊏]-minimum : (l ≡ ∅) ∨ (∅ ⊏ l)
[⊏]-minimum {∅}     = [∨]-introₗ [≡]-intro
[⊏]-minimum {x ⊰ l} = [∨]-introᵣ (skip [⊑]-minimum)

[⊏]-emptyₗ : (∅ ⊏ (x ⊰ l))
[⊏]-emptyₗ {l = ∅}     = skip empty
[⊏]-emptyₗ {l = x ⊰ l} = skip ([⊏]-to-[⊑] ([⊏]-emptyₗ {l = l}))

[⊏]-emptyᵣ : ¬(l ⊏ ∅)
[⊏]-emptyᵣ ()

[⊏]-length : (l₁ ⊏ l₂) → (length(l₁) < length(l₂))
[⊏]-length (use  p) = [≤]-with-[𝐒] ⦃ [⊏]-length p ⦄
[⊏]-length (skip p) = [≤]-with-[𝐒] ⦃ [⊑]-length p ⦄

[⊏]-prepend : (l ⊏ x ⊰ l)
[⊏]-prepend = skip [⊑]-reflexivity

[⊏]-postpend : (l ⊏ postpend x l)
[⊏]-postpend {∅}     = skip empty
[⊏]-postpend {a ⊰ l} = use ([⊏]-postpend {l})

[⊏]-map : ∀{f : T → T₂} → (l₁ ⊏ l₂) → (map f(l₁) ⊏ map f(l₂))
[⊏]-map (use  p) = use ([⊏]-map p)
[⊏]-map (skip p) = skip ([⊑]-map p)

[⊏]-tail : (∅ ⊏ l) → (tail l ⊏ l)
[⊏]-tail (skip _) = skip [⊑]-reflexivity

[⊏]-initial : (n < length(l)) → (initial n l ⊏ l)
[⊏]-initial {𝟎}   {x ⊰ l} p = [⊏]-emptyₗ
[⊏]-initial {𝐒 n} {x ⊰ l} p = use ([⊏]-initial {n} ([≤]-without-[𝐒] p))

[⊏]-skip : (𝟎 < n) → (n < length(l)) → (List.skip n l ⊏ l)
[⊏]-skip {𝐒 n} {x ⊰ l} p q = skip [⊑]-skip

[⊏]-withoutIndex : (n < length(l)) → (withoutIndex n l ⊏ l)
[⊏]-withoutIndex {𝟎}   {x ⊰ l} p = [⊏]-prepend
[⊏]-withoutIndex {𝐒 n} {x ⊰ l} p = use ([⊏]-withoutIndex ([≤]-without-[𝐒] p))

[⊏]-separate₂ : let (l₁ , l₂) = separate₂(l) in (2 ≤ length(l)) → ((l₁ ⊏ l) ∧ (l₂ ⊏ l))
[⊏]-separate₂ {x ⊰ ∅}     (succ())
Tuple.left  ([⊏]-separate₂ {x ⊰ y ⊰ l} (succ (succ min))) = use (skip (Tuple.left  [⊑]-separate₂))
Tuple.right ([⊏]-separate₂ {x ⊰ y ⊰ l} (succ (succ min))) = skip (use (Tuple.right [⊑]-separate₂))

[⊏]ᵣ-of-[++]ₗ : (∅ ⊏ l₂) → (l₁ ⊏ (l₂ ++ l₁))
[⊏]ᵣ-of-[++]ₗ {a ⊰ l₂} {l₁} (skip p) = skip([⊑]ᵣ-of-[++]ₗ {l₁}{l₂})

[⊏]ᵣ-of-[++]ᵣ : (∅ ⊏ l₂) → (l₁ ⊏ (l₁ ++ l₂))
[⊏]ᵣ-of-[++]ᵣ {a ⊰ l₂} {∅}      (skip p) = skip p
[⊏]ᵣ-of-[++]ᵣ {a ⊰ l₂} {b ⊰ l₁} (skip p) = use ([⊏]ᵣ-of-[++]ᵣ {a ⊰ l₂} {l₁} (skip p))

[⊑][⊏]-transitivity-like : (l₁ ⊑ l₂) → (l₂ ⊏ l₃) → (l₁ ⊏ l₃)
[⊑][⊏]-transitivity-like p        (skip q) = skip([⊑]-transitivity p q)
[⊑][⊏]-transitivity-like (use  p) (use  q) = use ([⊑][⊏]-transitivity-like p q)
[⊑][⊏]-transitivity-like (skip p) (use  q) = [⊏]-skip-[⊰] ([⊑][⊏]-transitivity-like p q)

instance
  [⊏][<]-on-length-sub : (_⊏_ {T = T}) ⊆₂ ((_<_) on₂ length)
  [⊏][<]-on-length-sub = intro [⊏]-length

module _ where
  open Structure.Relator.Ordering.Strict.Properties

  instance
    [<]-on-length-well-founded : WellFounded((_<_) on₂ (length {T = T}))
    [<]-on-length-well-founded = wellfounded-image-by-trans

  instance
    [⊏]-well-founded : WellFounded(_⊏_ {T = T})
    [⊏]-well-founded = accessibleₗ-sub₂ ⦃ [⊏][<]-on-length-sub ⦄

[⊑]-to-[⊏] : (l₁ ⊑ l₂) → ((l₁ ⊏ l₂) ∨ (length(l₁) ≡ length(l₂)))
[⊑]-to-[⊏] empty    = [∨]-introᵣ [≡]-intro
[⊑]-to-[⊏] (use p)  = Either.map use ([≡]-with(𝐒)) ([⊑]-to-[⊏] p)
[⊑]-to-[⊏] (skip p) = [∨]-introₗ (skip p)
