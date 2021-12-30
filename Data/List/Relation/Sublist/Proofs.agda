import      Lvl
open import Structure.Setoid
open import Type

module Data.List.Relation.Sublist.Proofs {ℓ ℓₑ} {T : Type{ℓ}} ⦃ equiv : Equiv{ℓₑ}(T) ⦄ where

open import Data.Boolean
import      Data.Either as Either
open import Data.List as List
open import Data.List.Equiv
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
open import Relator.Equals using () renaming (_≡_ to _≡ₑ_ ; [≡]-intro to [≡ₑ]-intro)
open import Structure.Function
open import Structure.Operator
open import Structure.Relator
import      Structure.Relator.Names as Names
open import Structure.Relator.Ordering
open import Structure.Relator.Ordering.Proofs
open import Structure.Relator.Properties
open import Syntax.Transitivity

private variable ℓ₂ : Lvl.Level
private variable T₂ : Type{ℓ₂}
private variable a x y : T
private variable l l₁ l₂ l₃ : List(T)
private variable n : ℕ

----------------------------------------------------------------------------------------------
-- Fundamental stuff on (_⊑_)

[⊑]-without-[⊰] : ((x ⊰ l₁) ⊑ (y ⊰ l₂)) → (l₁ ⊑ l₂)
[⊑]-without-[⊰]                (use _ p)       = p
[⊑]-without-[⊰]                (skip(use _ p)) = skip p
[⊑]-without-[⊰] {x = x}{y = y} (skip(skip p))  = skip([⊑]-without-[⊰] {x = x}{y = y} (skip p))

[⊑]-not-prepend : ¬((x ⊰ l) ⊑ l)
[⊑]-not-prepend {x} {y ⊰ l₂} (use xy p) = [⊑]-not-prepend {y}{l₂} p
[⊑]-not-prepend {x} {y ⊰ _}  (skip   p) = [⊑]-not-prepend([⊑]-without-[⊰] {y = y} (skip p))

module _ {ℓₑₗ} ⦃ equiv-List : Equiv{ℓₑₗ}(List(T)) ⦄ where
  [⊑]-empty : (l ⊑ ∅) → (l ≡ ∅)
  [⊑]-empty {∅}     _ = reflexivity(_≡_)
  [⊑]-empty {_ ⊰ _} ()

----------------------------------------------------------------------------------------------
-- Order related on (_⊑_)

instance
  [⊑]-reflexivity : Reflexivity(_⊑_ {T = T})
  [⊑]-reflexivity = intro p where
    p : Names.Reflexivity(_⊑_)
    p{∅}     = empty
    p{a ⊰ l} = use (reflexivity(_≡_)) (p{l})

instance
  [⊑]-transitivity : Transitivity(_⊑_ {T = T})
  [⊑]-transitivity = intro p where
    p : Names.Transitivity(_⊑_)
    p empty         empty         = empty
    p empty         (skip   l₂l₃) = skip l₂l₃
    p (use xy l₁l₂) (use yz l₂l₃) = use (xy 🝖 yz) (p l₁l₂ l₂l₃)
    p (use xy l₁l₂) (skip   l₂l₃) = skip(p (use xy l₁l₂) l₂l₃)
    p (skip l₁l₂)   (use yz l₂l₃) = skip(p l₁l₂ l₂l₃)
    p (skip l₁l₂)   (skip   l₂l₃) = skip(p (skip l₁l₂) l₂l₃)

module _ {ℓₑₗ} ⦃ equiv-List : Equiv{ℓₑₗ}(List(T)) ⦄ ⦃ ext : Extensionality(equiv-List) ⦄ where
  instance
    [⊑]-antisymmetry : Antisymmetry(_⊑_ {T = T})(_≡_)
    [⊑]-antisymmetry = intro p where
      p : Names.Antisymmetry(_⊑_)(_≡_)
      p {∅}      {∅}      sup sub = reflexivity(_≡_)
      p {x ⊰ l₁} {y ⊰ l₂} (use yx sup) (use xy sub) = congruence₂(_⊰_) yx (p sup sub)
      p {x ⊰ l₁} {y ⊰ l₂} (use yx sup) (skip   sub) with () ← [⊑]-not-prepend (transitivity(_⊑_) sub sup)
      p {x ⊰ l₁} {y ⊰ l₂} (skip   sup) (use xy sub) with () ← [⊑]-not-prepend (transitivity(_⊑_) sup sub)
      p {x ⊰ l₁} {y ⊰ l₂} (skip   sup) (skip   sub) with () ← [⊑]-not-prepend (transitivity(_⊑_) (skip sub) sup)

  {-
  instance
    [⊑]-antisymmetry : Antisymmetry(_⊑_ {T = T})(_≡_)
    [⊑]-antisymmetry = intro p where
      p : Names.Antisymmetry(_⊑_)(_≡_)
      p {∅}      {∅}       l          r        = reflexivity(_≡_)
      p {x ⊰ l₂} {y ⊰ l₁} (use xy l)  r        = congruence₂(_⊰_) xy (p l ([⊑]-without-[⊰] r))
      p {x ⊰ l₂} {y ⊰ l₁} (skip l) (use xy r)  = congruence₂(_⊰_) (symmetry(_≡_) xy) (p ([⊑]-without-[⊰] {y = y} (skip l)) r)
      p {y ⊰ l₂} {x ⊰ l₁} (skip l) (skip r)    = [⊥]-elim ([⊑]-not-prepend (transitivity(_⊑_) (skip r) l))
  -}

  [≡][⊒][⊑]-equivalence : ∀{l₁ l₂} → (l₁ ≡ l₂) ↔ ((l₁ ⊒ l₂) ∧ (l₁ ⊑ l₂))
  [≡][⊒][⊑]-equivalence = [↔]-intro (Tuple.uncurry(swap(antisymmetry(_⊑_)(_≡_)))) R where
    R : ∀{l₁ l₂} → (l₁ ≡ l₂) → ((l₁ ⊒ l₂) ∧ (l₁ ⊑ l₂))
    R {∅}      {∅}      eq = [∧]-intro empty empty
    R {∅}      {x ⊰ l₂} eq with () ← [∅][⊰]-unequal eq
    R {x ⊰ l₁} {∅}      eq with () ← [∅][⊰]-unequal (symmetry(_≡_) eq)
    R {x ⊰ l₁} {y ⊰ l₂} eq =
      let
        [∧]-intro eq1 eq2 = R{l₁}{l₂} ([⊰]-generalized-cancellationₗ eq)
        xy = [⊰]-generalized-cancellationᵣ eq
      in [∧]-intro  (use (symmetry(_≡_) xy) eq1) (use xy eq2)

  instance
    [≡][⊒]-sub : (_≡_) ⊆₂ (_⊒_)
    [≡][⊒]-sub = intro([∧]-elimₗ ∘ [↔]-to-[→] [≡][⊒][⊑]-equivalence)

  instance
    [≡][⊑]-sub : (_≡_) ⊆₂ (_⊑_)
    [≡][⊑]-sub = intro([∧]-elimᵣ ∘ [↔]-to-[→] [≡][⊒][⊑]-equivalence)

  instance
    [⊑]-relator : BinaryRelator(_⊑_ {T = T})
    [⊑]-relator = BinaryRelator-introᵣ \xy1 xy2 sub → sub₂(_≡_)(_⊒_) xy1 🝖 sub 🝖 sub₂(_≡_)(_⊑_) xy2

  instance
    [⊑]-weakPartialOrder : Weak.PartialOrder(_⊑_ {T = T})
    [⊑]-weakPartialOrder = record{}

[⊑]-minimum : (∅ ⊑ l)
[⊑]-minimum {∅}     = empty
[⊑]-minimum {a ⊰ l} = skip([⊑]-minimum{l})

----------------------------------------------------------------------------------------------
-- List functions on (_⊑_)

[⊑]-prepend : (l ⊑ x ⊰ l)
[⊑]-prepend {∅}     = skip empty
[⊑]-prepend {x ⊰ l} = skip (reflexivity(_⊑_))

[⊑]ᵣ-of-[++]ₗ : (l₁ ⊑ (l₂ ++ l₁))
[⊑]ᵣ-of-[++]ₗ {l₁}{∅}      = reflexivity(_⊑_)
[⊑]ᵣ-of-[++]ₗ {l₁}{a ⊰ l₂} = skip{x = a}([⊑]ᵣ-of-[++]ₗ {l₁}{l₂})

[⊑]ᵣ-of-[++]ᵣ : (l₁ ⊑ (l₁ ++ l₂))
[⊑]ᵣ-of-[++]ᵣ {∅}     {l₂} = [⊑]-minimum
[⊑]ᵣ-of-[++]ᵣ {a ⊰ l₁}{l₂} = use (reflexivity(_≡_)) ([⊑]ᵣ-of-[++]ᵣ{l₁}{l₂})

[⊑]-tail : (tail l ⊑ l)
[⊑]-tail {∅}     = empty
[⊑]-tail {a ⊰ l} = skip (reflexivity(_⊑_))

module _ {ℓₑ₂} ⦃ equiv₂ : Equiv{ℓₑ₂}(T₂) ⦄ {f : T → T₂} ⦃ func : Function(f) ⦄ where
  [⊑]-map : (l₁ ⊑ l₂) → (map f(l₁) ⊑ map f(l₂))
  [⊑]-map empty      = empty
  [⊑]-map (use eq p) = use (congruence₁(_) eq) ([⊑]-map p)
  [⊑]-map (skip p)   = skip ([⊑]-map p)

[⊑]-filter : ∀{f} → (filter f(l) ⊑ l)
[⊑]-filter {∅}         = empty
[⊑]-filter {x ⊰ l} {f} with f(x)
... | 𝑇 = use (reflexivity(_≡_)) ([⊑]-filter {l})
... | 𝐹 = skip ([⊑]-filter {l})

[⊑]-separate₂ : let (l₁ , l₂) = separate₂(l) in (l₁ ⊑ l) ∧ (l₂ ⊑ l)
Tuple.left  ([⊑]-separate₂ {∅})         = empty
Tuple.left  ([⊑]-separate₂ {x ⊰ ∅})     = reflexivity(_⊑_)
Tuple.left  ([⊑]-separate₂ {x ⊰ y ⊰ l}) = use (reflexivity(_≡_)) (skip (Tuple.left [⊑]-separate₂))
Tuple.right ([⊑]-separate₂ {∅})         = empty
Tuple.right ([⊑]-separate₂ {x ⊰ ∅})     = skip (reflexivity(_⊑_))
Tuple.right ([⊑]-separate₂ {x ⊰ y ⊰ l}) = skip (use (reflexivity(_≡_)) (Tuple.right [⊑]-separate₂))

[⊑]-postpend : (l ⊑ postpend a l)
[⊑]-postpend {∅}     = skip empty
[⊑]-postpend {x ⊰ l} = use (reflexivity(_≡_)) [⊑]-postpend

[⊑]-withoutIndex : (withoutIndex n l ⊑ l)
[⊑]-withoutIndex {𝟎}   {∅}     = empty
[⊑]-withoutIndex {𝐒 n} {∅}     = empty
[⊑]-withoutIndex {𝟎}   {x ⊰ l} = skip (reflexivity(_⊑_))
[⊑]-withoutIndex {𝐒 n} {x ⊰ l} = use (reflexivity(_≡_)) [⊑]-withoutIndex

[⊑]-initial : (initial n l ⊑ l)
[⊑]-initial {𝟎}   {∅}     = empty
[⊑]-initial {𝐒 n} {∅}     = empty
[⊑]-initial {𝟎}   {x ⊰ l} = [⊑]-minimum
[⊑]-initial {𝐒 n} {x ⊰ l} = use (reflexivity(_≡_)) [⊑]-initial

[⊑]-skip : (List.skip n l ⊑ l)
[⊑]-skip {𝟎}   {∅}     = empty
[⊑]-skip {𝐒 n} {∅}     = empty
[⊑]-skip {𝟎}   {x ⊰ l} = reflexivity(_⊑_)
[⊑]-skip {𝐒 n} {x ⊰ l} = skip [⊑]-skip

[⊑]-length : (l₁ ⊑ l₂) → (length(l₁) ≤ length(l₂))
[⊑]-length empty     = [≤]-minimum
[⊑]-length (use _ p) = [≤]-with-[𝐒] ⦃ [⊑]-length p ⦄
[⊑]-length (skip  p) = [≤]-predecessor ([≤]-with-[𝐒] ⦃ [⊑]-length p ⦄)

----------------------------------------------------------------------------------------------
-- Fundamental stuff on (_⊏_)

[⊏]-without-[⊰] : ((x ⊰ l₁) ⊏ (y ⊰ l₂)) → (l₁ ⊏ l₂)
[⊏]-without-[⊰]                (use _ p)         = p
[⊏]-without-[⊰]                (skip (use _ p))  = skip p
[⊏]-without-[⊰] {x = x}{y = y} (skip (skip p)) = skip ([⊑]-without-[⊰] {x = x}{y = y} (skip p))

[⊏]-to-[⊑] : (l₁ ⊏ l₂) → (l₁ ⊑ l₂)
[⊏]-to-[⊑] (use xy p) = use xy ([⊏]-to-[⊑] p)
[⊏]-to-[⊑] (skip   p) = skip p

[⊏]-skip-[⊰] : (l₁ ⊏ l₂) → (l₁ ⊏ (x ⊰ l₂))
[⊏]-skip-[⊰] (use xy p) = skip ([⊏]-to-[⊑] (use xy p))
[⊏]-skip-[⊰] (skip   p) = skip (skip p)

[⊏]-emptyₗ : (∅ ⊏ (x ⊰ l))
[⊏]-emptyₗ {l = ∅}     = skip empty
[⊏]-emptyₗ {l = x ⊰ l} = skip ([⊏]-to-[⊑] ([⊏]-emptyₗ {l = l}))

[⊏]-emptyᵣ : ¬(l ⊏ ∅)
[⊏]-emptyᵣ ()

----------------------------------------------------------------------------------------------
-- Order related on (_⊏_)

instance
  [⊏]-irreflexivity : Irreflexivity(_⊏_ {T = T})
  [⊏]-irreflexivity = intro p where
    p : Names.Irreflexivity(_⊏_)
    p{∅}     ()
    p{x ⊰ l} prev = p{l} ([⊏]-without-[⊰] prev)

instance
  [⊏]-transitivity : Transitivity(_⊏_ {T = T})
  [⊏]-transitivity = intro proof where
    proof : Names.Transitivity(_⊏_ {T = T})
    proof p          (skip (skip q))    = skip(skip(transitivity(_⊑_) ([⊏]-to-[⊑] p) q))
    proof (use xy p) (use yz q)         = use (xy 🝖 yz) (proof p q)
    proof (use xy p) (skip (use yz q))  = skip (use (xy 🝖 yz) (transitivity(_⊑_) ([⊏]-to-[⊑] p) q))
    proof (skip p)   (use yz q)         = skip(transitivity(_⊑_) p ([⊏]-to-[⊑] q))
    proof (skip p)   (skip (use yz q))  = skip(skip(transitivity(_⊑_) p q))

instance
  [⊏]-asymmetry : Asymmetry(_⊏_)
  [⊏]-asymmetry = intro(irreflexivity(_⊏_) ∘₂ transitivity(_⊏_))

module _ {ℓₑₗ} ⦃ equiv-List : Equiv{ℓₑₗ}(List(T)) ⦄ where
  [⊏]-minimum : (l ≡ ∅) ∨ (∅ ⊏ l)
  [⊏]-minimum {∅}     = [∨]-introₗ (reflexivity(_≡_))
  [⊏]-minimum {x ⊰ l} = [∨]-introᵣ (skip [⊑]-minimum)

----------------------------------------------------------------------------------------------
-- List functions on (_⊏_)

[⊏]-length : (l₁ ⊏ l₂) → (length(l₁) < length(l₂))
[⊏]-length (use _ p) = [≤]-with-[𝐒] ⦃ [⊏]-length p ⦄
[⊏]-length (skip  p) = [≤]-with-[𝐒] ⦃ [⊑]-length p ⦄

[⊏]-prepend : (l ⊏ x ⊰ l)
[⊏]-prepend = skip (reflexivity(_⊑_))

[⊏]-postpend : (l ⊏ postpend x l)
[⊏]-postpend {∅}     = skip empty
[⊏]-postpend {a ⊰ l} = use (reflexivity(_≡_)) ([⊏]-postpend {l})

module _ {ℓₑ₂} ⦃ equiv₂ : Equiv{ℓₑ₂}(T₂) ⦄ {f : T → T₂} ⦃ func : Function(f) ⦄ where
  [⊏]-map : (l₁ ⊏ l₂) → (map f(l₁) ⊏ map f(l₂))
  [⊏]-map (use xy p) = use (congruence₁(f) xy) ([⊏]-map p)
  [⊏]-map (skip   p) = skip ([⊑]-map p)

[⊏]-tail : (∅ ⊏ l) → (tail l ⊏ l)
[⊏]-tail (skip _) = skip (reflexivity(_⊑_))

[⊏]-initial : (n < length(l)) → (initial n l ⊏ l)
[⊏]-initial {𝟎}   {x ⊰ l} p = [⊏]-emptyₗ
[⊏]-initial {𝐒 n} {x ⊰ l} p = use (reflexivity(_≡_)) ([⊏]-initial {n} ([≤]-without-[𝐒] p))

[⊏]-skip : (𝟎 < n) → (n < length(l)) → (List.skip n l ⊏ l)
[⊏]-skip {𝐒 n} {x ⊰ l} p q = skip [⊑]-skip

[⊏]-withoutIndex : (n < length(l)) → (withoutIndex n l ⊏ l)
[⊏]-withoutIndex {𝟎}   {x ⊰ l} p = [⊏]-prepend
[⊏]-withoutIndex {𝐒 n} {x ⊰ l} p = use (reflexivity(_≡_)) ([⊏]-withoutIndex ([≤]-without-[𝐒] p))

[⊏]-separate₂ : let (l₁ , l₂) = separate₂(l) in (2 ≤ length(l)) → ((l₁ ⊏ l) ∧ (l₂ ⊏ l))
[⊏]-separate₂ {x ⊰ ∅}     (succ())
Tuple.left  ([⊏]-separate₂ {x ⊰ y ⊰ l} (succ (succ min))) = use (reflexivity(_≡_)) (skip (Tuple.left  [⊑]-separate₂))
Tuple.right ([⊏]-separate₂ {x ⊰ y ⊰ l} (succ (succ min))) = skip (use (reflexivity(_≡_)) (Tuple.right [⊑]-separate₂))

[⊏]ᵣ-of-[++]ₗ : (∅ ⊏ l₂) → (l₁ ⊏ (l₂ ++ l₁))
[⊏]ᵣ-of-[++]ₗ {a ⊰ l₂} {l₁} (skip p) = skip([⊑]ᵣ-of-[++]ₗ {l₁}{l₂})

[⊏]ᵣ-of-[++]ᵣ : (∅ ⊏ l₂) → (l₁ ⊏ (l₁ ++ l₂))
[⊏]ᵣ-of-[++]ᵣ {a ⊰ l₂} {∅}      (skip p) = skip p
[⊏]ᵣ-of-[++]ᵣ {a ⊰ l₂} {b ⊰ l₁} (skip p) = use (reflexivity(_≡_)) ([⊏]ᵣ-of-[++]ᵣ {a ⊰ l₂} {l₁} (skip p))

module _ {_≤?_ : T → T → Bool} where
  open import Data using (Unit ; <>)
  open import Data.List.Sorting.Functions(_≤?_)
  import      Data.Option as Option
  import      Data.Option.Functions as Option

  [⊏]-extractMinimal : Option.partialMap Unit (\{(_ , sl) → sl ⊏ l}) (extractMinimal l)
  [⊏]-extractMinimal {∅} = <>
  [⊏]-extractMinimal {x ⊰ ∅} = skip empty
  [⊏]-extractMinimal {x ⊰ l@(_ ⊰ _)} with extractMinimal l | [⊏]-extractMinimal{l}
  ... | Option.None         | _ = <>
  ... | Option.Some(y , ll) | p with (x ≤? y)
  ... | 𝑇 = skip (reflexivity(_⊑_))
  ... | 𝐹 = use (reflexivity(_≡_)) p

----------------------------------------------------------------------------------------------
-- Order related 2 on (_⊏_)

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

----------------------------------------------------------------------------------------------
-- Relating the weak and strict order ((_⊏_) and (_⊑_))

instance
  [⊏][⊑]-subtransitivityₗ : Subtransitivityₗ(_⊏_)(_⊑_)
  [⊏][⊑]-subtransitivityₗ = intro proof where
    proof : (l₁ ⊑ l₂) → (l₂ ⊏ l₃) → (l₁ ⊏ l₃)
    proof p          (skip   q) = skip(transitivity(_⊑_) p q)
    proof (use xy p) (use yz q) = use (xy 🝖 yz) (proof p q)
    proof (skip   p) (use yz q) = [⊏]-skip-[⊰] (proof p q)

instance
  [⊏][⊑]-sub : (_⊏_) ⊆₂ (_⊑_)
  [⊏][⊑]-sub = intro p where
    p : Names.Subrelation(_⊏_)(_⊑_)
    p (use xy l₁l₂) = use xy (p l₁l₂)
    p (skip xl₂)    = skip xl₂

module _ {ℓₑₗ} ⦃ equiv-List : Equiv{ℓₑₗ}(List(T)) ⦄ ⦃ ext : Extensionality(equiv-List) ⦄ where
  [⊑]-to-[⊏] : (l₁ ⊑ l₂) → ((l₁ ⊏ l₂) ∨ (l₁ ≡ l₂))
  [⊑]-to-[⊏] empty      = [∨]-introᵣ (reflexivity(_≡_))
  [⊑]-to-[⊏] (use xy p) = Either.map (use xy) (congruence₂(_⊰_) xy) ([⊑]-to-[⊏] p)
  [⊑]-to-[⊏] (skip p)   = [∨]-introₗ (skip p)
