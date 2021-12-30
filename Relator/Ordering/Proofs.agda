module Relator.Ordering.Proofs where

open import Data
import      Lvl
open import Functional
open import Functional.Instance
open import Logic
open import Logic.Classical
open import Logic.Propositional
open import Logic.Propositional.Theorems
open import Type
import      Relator.Ordering
open import Structure.Relator.Ordering
import      Structure.Relator.Ordering.Proofs as Ord
import      Structure.Relator.Names as Names
open import Structure.Relator.Proofs
open import Structure.Relator.Properties
open import Structure.Relator.Properties.Proofs
open import Structure.Relator
open import Structure.Setoid
open import Syntax.Implication
open import Syntax.Transitivity

private variable ℓ ℓ₁ ℓ₂ ℓ₃ ℓₗ ℓₑ ℓₗₑ ℓₗₜ : Lvl.Level
private variable T : Type{ℓ}

module From-[≤] (_≤_ : T → T → Stmt{ℓₗ}) where
  open Relator.Ordering.From-[≤] (_≤_)

  module ByNothing where
    [≤][>]-not : ∀{a b} → (a ≤ b) → (a > b) → ⊥
    [≤][>]-not = apply

    [≥][<]-not : ∀{a b} → (a ≥ b) → (a < b) → ⊥
    [≥][<]-not = apply

  module ByTotalOrder ⦃ equiv : Equiv{ℓₑ}(T) ⦄ ⦃ _ : Weak.TotalOrder(_≤_) ⦄ where
    open ByNothing public

    [<]-to-[≤] : Names.Subrelation(_<_)(_≤_)
    [<]-to-[≤] {a} {b} nba with converseTotal(_≤_){a}{b}
    [<]-to-[≤] {a} {b} nba | [∨]-introₗ ab = ab
    [<]-to-[≤] {a} {b} nba | [∨]-introᵣ ba = [⊥]-elim(nba ba)
    instance
      [<][≤]-sub : (_<_) ⊆₂ (_≤_)
      _⊆₂_.proof [<][≤]-sub = [<]-to-[≤]

    [>]-to-[≥] : Names.Subrelation(_>_)(_≥_)
    [>]-to-[≥] = [<]-to-[≤]

    [>][≥]-sub : (_>_) ⊆₂ (_≥_)
    _⊆₂_.proof [>][≥]-sub = [>]-to-[≥]

    instance
      [<]-relator : BinaryRelator(_<_)
      [<]-relator = BinaryRelator-introᵣ(\xy1 xy2 → _∘ substitute₂ᵣ(_≤_) (symmetry(_≡_) xy2) (symmetry(_≡_) xy1))

    instance
      [<]-irreflexivity : Irreflexivity(_<_)
      Irreflexivity.proof [<]-irreflexivity = [¬¬]-intro(reflexivity(_≤_))

    instance
      [<]-transitivity : Transitivity(_<_)
      Transitivity.proof [<]-transitivity {a} {b} {c} nba ncb ca = [≤][>]-not (transitivity(_≤_) ca ([<]-to-[≤] nba)) ncb

    instance
      [<]-asymmetry : Asymmetry(_<_) -- TODO: Proof of this property is independent of the model. Actually, there are many of them here
      [<]-asymmetry = [irreflexivity,transitivity]-to-asymmetry

    [<]-strictOrder : Strict.PartialOrder(_<_)
    [<]-strictOrder = Strict.intro

    {- TODO: Maybe one must assume decidability of (_≡_)?
    instance
      [<]-total : ConverseTotal(_<_)
      ConverseTotal.proof [<]-total {x} {y} with converseTotal(_≤_)
      ... | [∨]-introₗ x₁ = {!!}
      ... | [∨]-introᵣ x₁ = {!!}
    -}

    instance
      [<][≤]-subtransitivityₗ : Subtransitivityₗ(_<_)(_≤_)
      Subtransitivityₗ.proof [<][≤]-subtransitivityₗ xy yz zx = yz(transitivity(_≤_) zx xy)

    instance
      [<][≤]-subtransitivityᵣ : Subtransitivityᵣ(_<_)(_≤_)
      Subtransitivityᵣ.proof [<][≤]-subtransitivityᵣ xy yz zx = xy(transitivity(_≤_) yz zx)

    [≤][≢]-to-[<] : ∀{a b} → (a ≤ b) → (a ≢ b) → (a < b)
    [≤][≢]-to-[<] le ne ba = ne(antisymmetry(_≤_)(_≡_) le ba)

    [≥][≢]-to-[>] : ∀{a b} → (a ≥ b) → (a ≢ b) → (a > b)
    [≥][≢]-to-[>] ge ne = [≤][≢]-to-[<] ge (ne ∘ symmetry(_≡_))

    instance
      [≡][≤]-sub : (_≡_) ⊆₂ (_≤_)
      [≡][≤]-sub = Ord.[≡][≤]-sub

    instance
      [≤][≡]-subtransitivityₗ : Subtransitivityₗ(_≤_)(_≡_)
      [≤][≡]-subtransitivityₗ = subrelation-transitivity-to-subtransitivityₗ

    instance
      [≤][≡]-subtransitivityᵣ : Subtransitivityᵣ(_≤_)(_≡_)
      [≤][≡]-subtransitivityᵣ = subrelation-transitivity-to-subtransitivityᵣ

    [≡]-to-[≥] : Names.Subrelation(_≡_)(_≥_)
    [≡]-to-[≥] = sub₂(_≡_)(_≤_) ∘ symmetry(_≡_)
    instance
      [≡][≥]-sub : (_≡_) ⊆₂ (_≥_)
      _⊆₂_.proof [≡][≥]-sub = [≡]-to-[≥]

    [≡][>]-not : ∀{a b} → (a ≡ b) → (a > b) → ⊥
    [≡][>]-not eq gt = [≤][>]-not (sub₂(_≡_)(_≤_) eq) gt

    instance
      [≡][≯]-sub : (_≡_) ⊆₂ (_≯_)
      _⊆₂_.proof [≡][≯]-sub = [≡][>]-not

    instance
      [>][≢]-sub : (_>_) ⊆₂ (_≢_)
      _⊆₂_.proof [>][≢]-sub = swap [≡][>]-not

    [≡][<]-not : ∀{a b} → (a ≡ b) → (a < b) → ⊥
    [≡][<]-not eq lt = [≤][>]-not ([≡]-to-[≥] eq) lt

    instance
      [≡][≮]-sub : (_≡_) ⊆₂ (_≮_)
      _⊆₂_.proof [≡][≮]-sub = [≡][<]-not

    instance
      [<][≢]-sub : (_<_) ⊆₂ (_≢_)
      _⊆₂_.proof [<][≢]-sub = swap [≡][<]-not

    instance
      [<][≡]-subtransitivityₗ : Subtransitivityₗ(_<_)(_≡_)
      Subtransitivityₗ.proof [<][≡]-subtransitivityₗ xy yz zx = [≡][>]-not xy (subtransitivityᵣ(_<_)(_≤_) yz zx)

    instance
      [<][≡]-subtransitivityᵣ : Subtransitivityᵣ(_<_)(_≡_)
      Subtransitivityᵣ.proof [<][≡]-subtransitivityᵣ xy yz zx = [≡][>]-not yz (subtransitivityₗ(_<_)(_≤_) zx xy)

  module ByClassicalTotalOrder ⦃ equiv : Equiv{ℓₑ}(T) ⦄ ⦃ totalOrder : Weak.TotalOrder(_≤_) ⦄ ⦃ [≡]-classical : Classical₂(_≡_) ⦄ where
    open ByTotalOrder ⦃ equiv ⦄ ⦃ totalOrder ⦄ public

    [≤]-or-[>] : ∀{a b} → (a ≤ b) ∨ (a > b)
    [≤]-or-[>] {a} {b} with converseTotal(_≤_){a}{b}
    [≤]-or-[>] {a} {b} | [∨]-introₗ ab = [∨]-introₗ ab
    [≤]-or-[>] {a} {b} | [∨]-introᵣ ba with excluded-middle _ ⦃ [≡]-classical {a}{b} ⦄
    [≤]-or-[>] {a} {b} | [∨]-introᵣ ba | [∨]-introₗ eqab  = [∨]-introₗ (sub₂(_≡_)(_≤_) ⦃ [≡][≤]-sub ⦄ eqab)
    [≤]-or-[>] {a} {b} | [∨]-introᵣ ba | [∨]-introᵣ neqab = [∨]-introᵣ (ab ↦ neqab(antisymmetry(_≤_)(_≡_) ab ba))

    instance
      [≤]-classical : Classical₂(_≤_)
      Classical.excluded-middle [≤]-classical = [≤]-or-[>]

    [≥]-or-[<] : ∀{a b} → (a ≥ b) ∨ (a < b)
    [≥]-or-[<] = [≤]-or-[>]

    [≥]-classical : Classical₂(_≥_)
    Classical.excluded-middle [≥]-classical = [≥]-or-[<]

    instance
      [<]-classical : Classical₂(_<_)
      Classical.excluded-middle ([<]-classical {a}{b}) with [≤]-or-[>] {b}{a}
      Classical.excluded-middle ([<]-classical {a}{b}) | [∨]-introₗ x = [∨]-introᵣ ([¬¬]-intro x)
      Classical.excluded-middle ([<]-classical {a}{b}) | [∨]-introᵣ x = [∨]-introₗ x

    [>]-classical : Classical₂(_>_)
    [>]-classical = [<]-classical

    [≤]-to-[<][≡] : ∀{a b} → (a ≤ b) → ((a < b) ∨ (a ≡ b))
    [≤]-to-[<][≡] {a} {b} ab with excluded-middle _ ⦃ [≡]-classical {a}{b} ⦄
    [≤]-to-[<][≡] {a} {b} ab | [∨]-introₗ eq = [∨]-introᵣ eq
    [≤]-to-[<][≡] {a} {b} ab | [∨]-introᵣ ne = [∨]-introₗ (ba ↦ ne(antisymmetry(_≤_)(_≡_) ab ba))

    [≥]-to-[>][≡] : ∀{a b} → (a ≥ b) → ((a > b) ∨ (a ≡ b))
    [≥]-to-[>][≡] ab = [∨]-elim2 id (symmetry(_≡_)) ([≤]-to-[<][≡] ab)

module From-[≤][≢] {ℓ₁ ℓ₂ ℓ₃} {T : Type{ℓ₁}} (_≤_ : T → T → Stmt{ℓ₂}) (_≢_ : T → T → Stmt{ℓ₃}) where
  open Relator.Ordering.From-[≤][≢] (_≤_)(_≢_)

  -- postulate instance [<]-totalOrder : Strict.TotalOrder(_<_)

  instance
    [<][≤]-sub : (_<_) ⊆₂ (_≤_)
    _⊆₂_.proof [<][≤]-sub = [∧]-elimₗ

  instance
    [>][≥]-sub : (_>_) ⊆₂ (_≥_)
    _⊆₂_.proof [>][≥]-sub = sub₂(_<_)(_≤_)

  instance
    [<][≢]-sub : (_<_) ⊆₂ (_≢_)
    _⊆₂_.proof [<][≢]-sub = [∧]-elimᵣ

  [>][≢]-sub : ⦃ sym : Symmetry(_≢_) ⦄ → ((_>_) ⊆₂ (_≢_))
  _⊆₂_.proof [>][≢]-sub = symmetry(_≢_) ∘ sub₂(_<_)(_≢_)

  -- [<]-transitivity : ⦃ [≤]-trans : Transitivity(_≤_) ⦄ → Transitivity(_<_)
  -- Transitivity.proof [<]-transitivity ([∧]-intro xy neq-xy) ([∧]-intro yz neq-yz) = [∧]-intro (transitivity(_≤_) xy yz) {!!} xy

  {-
  instance
    [<][≤]-subtransitivityₗ : Subtransitivityₗ(_<_)(_≤_)
    left (Subtransitivityₗ.proof [<][≤]-subtransitivityₗ xy ([∧]-intro yz nyz)) = transitivity(_≤_) xy yz
    Tuple.right (Subtransitivityₗ.proof [<][≤]-subtransitivityₗ xy yz) xz = {!!}
  postulate instance [<][≤]-subtransitivityᵣ : Subtransitivityᵣ(_<_)(_≤_)
  postulate instance [≤][≡]-subtransitivityₗ : Subtransitivityₗ(_≤_)(_≡_)
  postulate instance [≤][≡]-subtransitivityᵣ : Subtransitivityᵣ(_≤_)(_≡_)
  -}

module From-[≤][<]
  ⦃ equiv : Equiv{ℓₑ}(T) ⦄
  (_≤_ : T → T → Stmt{ℓₗₑ}) ⦃ [≤]-relator : BinaryRelator(_≤_) ⦄
  (_<_ : T → T → Stmt{ℓₗₜ}) ⦃ [<]-relator : BinaryRelator(_<_) ⦄
  where

  open Relator.Ordering.From-[≤][<] (_≤_)(_<_)

  private variable a b : T

  [≤]-def-[<][≡]ₗ-[<]-def-[≤][≢]ᵣ : ((∀{a b} → (a ≤ b) ← ((a < b) ∨ (a ≡ b))) ∧ Irreflexivity(_<_)) ↔ ((∀{a b} → (a < b) → ((a ≤ b) ∧ (a ≢ b))) ∧ Reflexivity(_≤_))
  [≤]-def-[<][≡]ₗ-[<]-def-[≤][≢]ᵣ = [↔]-intro (\([∧]-intro p q) → l p ⦃ q ⦄) (\([∧]-intro p q) → r p ⦃ q ⦄) where
    l : (∀{a b} → (a < b) → ((a ≤ b) ∧ (a ≢ b))) → ⦃ refl : Reflexivity(_≤_) ⦄ → ((∀{a b} → (a ≤ b) ← ((a < b) ∨ (a ≡ b))) ∧ Irreflexivity(_<_))
    l [<]-def-[≤][≢]ᵣ = [∧]-intro
      ([∨]-elim (lt ↦ [∧]-elimₗ ([<]-def-[≤][≢]ᵣ lt)) (sub₂(_≡_)(_≤_) ⦃ reflexive-rel-sub ⦄))
      (intro(xx ↦ [∧]-elimᵣ ([<]-def-[≤][≢]ᵣ xx) (reflexivity(_≡_))))

    r : (∀{a b} → (a ≤ b) ← ((a < b) ∨ (a ≡ b))) → ⦃ irrefl : Irreflexivity(_<_) ⦄ → ((∀{a b} → (a < b) → ((a ≤ b) ∧ (a ≢ b))) ∧ Reflexivity(_≤_))
    r [≤]-def-[<][≡]ᵣ = [∧]-intro
      (lt ↦ [∧]-intro ([≤]-def-[<][≡]ᵣ ([∨]-introₗ lt)) (eq ↦ empty(irreflexivity(_<_) (substitute₂-₁ᵣ(_<_)(_) eq lt))))
      (intro ([≤]-def-[<][≡]ᵣ ([∨]-introᵣ (reflexivity(_≡_)))))

  module By-[≤] ([<]-def-[≤][≢] : ∀{a b} → (a < b) ↔ ((a ≤ b) ∧ (a ≢ b))) where
    instance
      [<][≤]-sub : (_<_) ⊆₂ (_≤_)
      _⊆₂_.proof [<][≤]-sub = [∧]-elimₗ ∘ [↔]-to-[→] [<]-def-[≤][≢]

    instance
      [<][≢]-sub : (_<_) ⊆₂ (_≢_)
      _⊆₂_.proof [<][≢]-sub = [∧]-elimᵣ ∘ [↔]-to-[→] [<]-def-[≤][≢]

    module By-antisymmetry ⦃ antisym : Antisymmetry(_≤_)(_≡_) ⦄ where
      [≤][>]-not : ∀{a b : T} → (a ≤ b) → (a > b) → ⊥
      [≤][>]-not le gt =
        let [∧]-intro ge ne = [↔]-to-[→] [<]-def-[≤][≢] gt
        in ne(antisymmetry(_≤_)(_≡_) ge le)

      [≥][<]-not : ∀{a b : T} → (a ≥ b) → (a < b) → ⊥
      [≥][<]-not = [≤][>]-not

      [<]-asymmetry : Asymmetry(_<_)
      Asymmetry.proof [<]-asymmetry xy yx =
        let [∧]-intro xy-le nxy = [↔]-to-[→] [<]-def-[≤][≢] xy
            [∧]-intro yx-le nyx = [↔]-to-[→] [<]-def-[≤][≢] yx
        in  nxy(antisymmetry(_≤_)(_≡_) xy-le yx-le)

    module _ ⦃ [≡]-classical : ∀{a b : T} → Classical(a ≡ b) ⦄ where
      [≤]-def-[<][≡]ᵣ-by-classical : (a ≤ b) → ((a < b) ∨ (a ≡ b))
      [≤]-def-[<][≡]ᵣ-by-classical {a}{b} le with excluded-middle(a ≡ b)
      ... | [∨]-introₗ eq = [∨]-introᵣ eq
      ... | [∨]-introᵣ ne = [∨]-introₗ ([↔]-to-[←] [<]-def-[≤][≢] ([∧]-intro le ne))

    module _ ⦃ [<]-tri : ConverseTrichotomy(_<_)(_≡_) ⦄ ⦃ [≤]-antisym : Antisymmetry(_≤_)(_≡_) ⦄ where
      [≤]-def-[<][≡]ᵣ-by-tri-antisym : (a ≤ b) → ((a < b) ∨ (a ≡ b))
      [≤]-def-[<][≡]ᵣ-by-tri-antisym {a}{b} le with trichotomy(_<_)(_≡_) {a}{b}
      ... | [∨]-introₗ ([∨]-introₗ lt) = [∨]-introₗ lt
      ... | [∨]-introₗ ([∨]-introᵣ eq) = [∨]-introᵣ eq
      ... | [∨]-introᵣ             gt  = [∨]-introᵣ (antisymmetry(_≤_)(_≡_) le ([∧]-elimₗ ([↔]-to-[→] [<]-def-[≤][≢] gt)))

    instance
      [<]-irreflexivity : Irreflexivity(_<_)
      Irreflexivity.proof [<]-irreflexivity xx = [∧]-elimᵣ ([↔]-to-[→] [<]-def-[≤][≢] xx) (reflexivity(_≡_))

    [<]-transitivity-by-asym-trans : ⦃ antisym : Asymmetry(_<_) ⦄ → ⦃ trans : Transitivity(_≤_) ⦄ → Transitivity(_<_)
    Transitivity.proof [<]-transitivity-by-asym-trans xy yz =
      let [∧]-intro xy-le nxy = [↔]-to-[→] [<]-def-[≤][≢] xy
          [∧]-intro yz-le nyz = [↔]-to-[→] [<]-def-[≤][≢] yz
      in  [↔]-to-[←] [<]-def-[≤][≢] ([∧]-intro (transitivity(_≤_) xy-le yz-le) (xz ↦ asymmetry(_<_) (substitute₂-₁ᵣ(_<_)(_) xz xy) yz))

    module By-transitivity ⦃ trans : Transitivity(_≤_) ⦄ where
      instance
        [≤][<]-subtransitivityₗ : Subtransitivityₗ(_≤_)(_<_)
        Subtransitivityₗ.proof [≤][<]-subtransitivityₗ xy yz = [∧]-elimₗ ([↔]-to-[→] [<]-def-[≤][≢] xy) 🝖 yz

      instance
        [≤][<]-subtransitivityᵣ : Subtransitivityᵣ(_≤_)(_<_)
        Subtransitivityᵣ.proof [≤][<]-subtransitivityᵣ xy yz = xy 🝖 [∧]-elimₗ ([↔]-to-[→] [<]-def-[≤][≢] yz)

    module By-weakPartialOrder ⦃ refl : Reflexivity(_≤_) ⦄ ⦃ antisym : Antisymmetry(_≤_)(_≡_) ⦄ ⦃ trans : Transitivity(_≤_) ⦄ where
      instance
        [<][≤]-subtransitivityₗ : Subtransitivityₗ(_<_)(_≤_)
        Subtransitivityₗ.proof [<][≤]-subtransitivityₗ x≤y y<z =
          let [∧]-intro y≤z y≢z = [↔]-to-[→] [<]-def-[≤][≢] y<z
          in  [↔]-to-[←] [<]-def-[≤][≢] ([∧]-intro
            (x≤y 🝖 y≤z)
            (xz ↦ By-antisymmetry.[≤][>]-not (subtransitivityₗ(_≤_)(_≡_) ⦃ subrelation-transitivity-to-subtransitivityₗ ⦃ sub = reflexive-rel-sub ⦄ ⦄ (symmetry(_≡_) xz) x≤y) y<z))

      instance
        [<][≤]-subtransitivityᵣ : Subtransitivityᵣ(_<_)(_≤_)
        Subtransitivityᵣ.proof [<][≤]-subtransitivityᵣ x<y y≤z =
          let [∧]-intro x≤y x≢y = [↔]-to-[→] [<]-def-[≤][≢] x<y
          in  [↔]-to-[←] [<]-def-[≤][≢] ([∧]-intro
            (x≤y 🝖 y≤z)
            (xz ↦ By-antisymmetry.[≤][>]-not (subtransitivityᵣ(_≤_)(_≡_) ⦃ subrelation-transitivity-to-subtransitivityᵣ ⦃ sub = reflexive-rel-sub ⦄ ⦄ y≤z (symmetry(_≡_) xz)) x<y))

  module By-[<] ([≤]-def-[<][≡] : ∀{a b} → (a ≤ b) ↔ ((a < b) ∨ (a ≡ b))) where
    instance
      [<][≤]-sub : (_<_) ⊆₂ (_≤_)
      _⊆₂_.proof [<][≤]-sub = [↔]-to-[←] [≤]-def-[<][≡] ∘ [∨]-introₗ

    instance
      [≡][≤]-sub : (_≡_) ⊆₂ (_≤_)
      _⊆₂_.proof [≡][≤]-sub = [↔]-to-[←] [≤]-def-[<][≡] ∘ [∨]-introᵣ

    instance
      [≰][≮]-sub : (_≰_) ⊆₂ (_≮_)
      _⊆₂_.proof [≰][≮]-sub = contrapositiveᵣ(sub₂(_<_)(_≤_))

    instance
      [≰][≢]-sub : (_≰_) ⊆₂ (_≢_)
      _⊆₂_.proof [≰][≢]-sub = contrapositiveᵣ(sub₂(_≡_)(_≤_))

    instance
      [>][≥]-sub : (_>_) ⊆₂ (_≥_)
      _⊆₂_.proof [>][≥]-sub = sub₂(_<_)(_≤_)

    instance
      [≡][≥]-sub : (_≡_) ⊆₂ (_≥_)
      _⊆₂_.proof [≡][≥]-sub = sub₂(_≡_)(_≤_) ∘ symmetry(_≡_)

    instance
      [≱][≯]-sub : (_≱_) ⊆₂ (_≯_)
      _⊆₂_.proof [≱][≯]-sub = sub₂(_≰_)(_≮_)

    instance
      [≱][≢]-sub : (_≱_) ⊆₂ (_≢_)
      _⊆₂_.proof [≱][≢]-sub = (_∘ symmetry(_≡_)) ∘ sub₂(_≰_)(_≢_)

    [<]-def-[≤][≢]ₗ : (a < b) ← ((a ≤ b) ∧ (a ≢ b))
    [<]-def-[≤][≢]ₗ([∧]-intro le ne) = [∨]-elim id ([⊥]-elim ∘ ne) ([↔]-to-[→] [≤]-def-[<][≡] le)

    instance
      [≤]-reflexivity : Reflexivity(_≤_)
      Reflexivity.proof [≤]-reflexivity = [↔]-to-[←] [≤]-def-[<][≡] ([∨]-introᵣ (reflexivity(_≡_)))

    [≤]-transitivity-by-trans : ⦃ [<]-trans : Transitivity(_<_) ⦄ → Transitivity(_≤_)
    Transitivity.proof [≤]-transitivity-by-trans xy yz with [↔]-to-[→] [≤]-def-[<][≡] xy | [↔]-to-[→] [≤]-def-[<][≡] yz
    ... | [∨]-introₗ xy-lt | [∨]-introₗ yz-lt = [↔]-to-[←] [≤]-def-[<][≡] ([∨]-introₗ (transitivity(_<_) xy-lt yz-lt))
    ... | [∨]-introₗ xy-lt | [∨]-introᵣ yz-eq = [↔]-to-[←] [≤]-def-[<][≡] ([∨]-introₗ (substitute₂-₂ᵣ(_<_)(_) yz-eq xy-lt))
    ... | [∨]-introᵣ xy-eq | [∨]-introₗ yz-lt = [↔]-to-[←] [≤]-def-[<][≡] ([∨]-introₗ (substitute₂-₁ᵣ(_<_)(_) (symmetry(_≡_) xy-eq) yz-lt))
    ... | [∨]-introᵣ xy-eq | [∨]-introᵣ yz-eq = [↔]-to-[←] [≤]-def-[<][≡] ([∨]-introᵣ (transitivity(_≡_) xy-eq yz-eq))

    module _ ⦃ asym : Asymmetry(_<_) ⦄ where
      [≤]-antisymmetry-by-asym : Antisymmetry(_≤_)(_≡_)
      Antisymmetry.proof [≤]-antisymmetry-by-asym le ge with [↔]-to-[→] [≤]-def-[<][≡] le | [↔]-to-[→] [≤]-def-[<][≡] ge
      ... | [∨]-introₗ lt  | [∨]-introₗ gt  with () ← asymmetry(_<_) lt gt
      ... | [∨]-introₗ lt  | [∨]-introᵣ eq  = symmetry(_≡_) eq
      ... | [∨]-introᵣ eq  | [∨]-introₗ gt  = eq
      ... | [∨]-introᵣ eq₁ | [∨]-introᵣ eq₂ = eq₁

      [<]-transitivity-by-asym-trans : ⦃ trans : Transitivity(_≤_) ⦄ → Transitivity(_<_)
      Transitivity.proof [<]-transitivity-by-asym-trans {x}{y}{z} xy yz =
        • (
          • (xy ⇒
            (x < y) ⇒-[ [↔]-to-[←] [≤]-def-[<][≡] ∘ [∨]-introₗ ]
            (x ≤ y) ⇒-end
          )
          • (yz ⇒
            (y < z) ⇒-[ [↔]-to-[←] [≤]-def-[<][≡] ∘ [∨]-introₗ ]
            (y ≤ z) ⇒-end
          )
          ⇒₂-[ transitivity(_≤_) ]
          (x ≤ z)           ⇒-[ [↔]-to-[→] [≤]-def-[<][≡] ]
          (x < z) ∨ (x ≡ z) ⇒-end
        )
        • (
          (\xz →
            • (xz ⇒
              (x ≡ z) ⇒-[ apply xy ∘ substitute₂-₁ᵣ(_<_)(_) ]
              (z < y) ⇒-end
            )
            • (yz ⇒
              (y < z) ⇒-end
            )
            ⇒₂-[ asymmetry(_<_) ]
            ⊥       ⇒-end
          ) ⇒
          (x ≢ z) ⇒-end
        )
        ⇒₂-[ [∨]-not-right ]
        (x < z) ⇒-end

      [<][≱]-sub-by-asym : ((_<_) ⊆₂ (_≱_))
      _⊆₂_.proof [<][≱]-sub-by-asym lt-xy ge-xy = [∨]-elim
        (lt-yx ↦ asymmetry(_<_) lt-xy lt-yx)
        (eq-yx ↦ irreflexivity(_<_) ⦃ [asymmetry]-to-irreflexivity ⦄ (substitute₂-₂ᵣ(_<_)(_) eq-yx lt-xy))
        ([↔]-to-[→] [≤]-def-[<][≡] ge-xy)

      [>][≰]-sub-by-asym : ((_>_) ⊆₂ (_≰_))
      _⊆₂_.proof [>][≰]-sub-by-asym gt le = [∨]-elim
        (asymmetry(_<_) gt)
        (eq ↦ irreflexivity(_<_) ⦃ [asymmetry]-to-irreflexivity ⦄ (substitute₂-₂ᵣ(_<_)(_) eq gt))
        ([↔]-to-[→] [≤]-def-[<][≡] le)

    module _
      ⦃ [<]-classical : Classical₂(_<_) ⦄
      ⦃ [≡]-classical : Classical₂(_≡_) ⦄
      where

      [≤]-classical-by-classical : Classical₂(_≤_)
      Classical.excluded-middle ([≤]-classical-by-classical {x}{y}) with excluded-middle(x < y) | excluded-middle(x ≡ y)
      ... | [∨]-introₗ lt  | _             = [∨]-introₗ (sub₂(_<_)(_≤_) lt)
      ... | [∨]-introᵣ nlt | [∨]-introₗ eq = [∨]-introₗ (sub₂(_≡_)(_≤_) eq)
      ... | [∨]-introᵣ nlt | [∨]-introᵣ ne = [∨]-introᵣ (le ↦ nlt ([<]-def-[≤][≢]ₗ ([∧]-intro le ne)))

    module _
      ⦃ [<]-asym : Asymmetry(_<_) ⦄
      ⦃ [<]-total : ConverseTrichotomy(_<_)(_≡_) ⦄
      where

      [≤]-classical-by-asym-tri : Classical₂(_≤_)
      Classical.excluded-middle ([≤]-classical-by-asym-tri {x} {y}) with trichotomy(_<_)(_≡_) {x}{y}
      ... | [∨]-introₗ([∨]-introₗ lt) = [∨]-introₗ (sub₂(_<_)(_≤_) lt)
      ... | [∨]-introₗ([∨]-introᵣ eq) = [∨]-introₗ (sub₂(_≡_)(_≤_) eq)
      ... | [∨]-introᵣ            gt  =
        let [<]-def-[≤][≢]ᵣ = [∧]-elimₗ ([↔]-to-[→] [≤]-def-[<][≡]ₗ-[<]-def-[≤][≢]ᵣ ([∧]-intro ([↔]-to-[←] [≤]-def-[<][≡]) [asymmetry]-to-irreflexivity))
            [∧]-intro ge ne = [<]-def-[≤][≢]ᵣ gt
        in  [∨]-introᵣ (ne ∘ antisymmetry(_≤_)(_≡_) ⦃ [≤]-antisymmetry-by-asym ⦄ ge)

  -- TODO: Move to Structure.Relator.Properties.Proofs
  module _
    ⦃ [<]-asym : Asymmetry(_<_) ⦄
    ⦃ [<]-total : ConverseTrichotomy(_<_)(_≡_) ⦄
    where

    [<]-classical-by-asym-tri : Classical₂(_<_)
    Classical.excluded-middle ([<]-classical-by-asym-tri {x} {y}) with trichotomy(_<_)(_≡_) {x}{y}
    ... | [∨]-introₗ([∨]-introₗ lt) = [∨]-introₗ lt
    ... | [∨]-introₗ([∨]-introᵣ eq) = [∨]-introᵣ (lt ↦ irreflexivity(_<_) ⦃ [asymmetry]-to-irreflexivity ⦄ (substitute₂-₁ᵣ(_<_)(_) eq lt))
    ... | [∨]-introᵣ            gt  = [∨]-introᵣ (lt ↦ asymmetry(_<_) lt gt)

  module ByReflTriSub
    ⦃ [≤]-refl : Reflexivity(_≤_) ⦄
    ⦃ [<]-total : ConverseTrichotomy(_<_)(_≡_) ⦄
    ⦃ [<][≤]-sub : (_<_) ⊆₂ (_≤_) ⦄
    where

    [≰][≯]-not : (a ≰ b) → (a ≯ b) → ⊥
    [≰][≯]-not {a}{b} nle ngt with trichotomy(_<_)(_≡_) {a}{b}
    ... | [∨]-introₗ([∨]-introₗ lt) = nle (sub₂(_<_)(_≤_) lt)
    ... | [∨]-introₗ([∨]-introᵣ eq) = substitute₂-₁ᵣ(_≰_) ⦃ [¬]-binaryRelator ⦄ (_) eq nle (reflexivity(_≤_))
    ... | [∨]-introᵣ            gt  = ngt gt

    [≮][≱]-not : (a ≮ b) → (a ≱ b) → ⊥
    [≮][≱]-not = swap [≰][≯]-not

    module _ ⦃ [<]-classical : Classical₂(_<_) ⦄ where
      [≰][>]-sub : (_≰_) ⊆₂ (_>_)
      _⊆₂_.proof [≰][>]-sub = [¬¬]-elim ∘ [≰][≯]-not

      [≱][<]-sub : (_≱_) ⊆₂ (_<_)
      _⊆₂_.proof [≱][<]-sub = _⊆₂_.proof [≰][>]-sub

    module _ ⦃ [≤]-classical : Classical₂(_≤_) ⦄ where
      [≯][≤]-sub : (_≯_) ⊆₂ (_≤_)
      _⊆₂_.proof [≯][≤]-sub = [¬¬]-elim ∘ swap [≰][≯]-not

      [≮][≥]-sub : (_≮_) ⊆₂ (_≥_)
      _⊆₂_.proof [≮][≥]-sub = _⊆₂_.proof [≯][≤]-sub

    module _
      ⦃ [≤]-classical : Classical₂(_≤_) ⦄
      ⦃ [<]-classical : Classical₂(_<_) ⦄
      where

      [≤]-or-[>] : (a ≤ b) ∨ (a > b)
      [≤]-or-[>] {a}{b} with excluded-middle(a ≤ b)
      ... | [∨]-introₗ a≤b = [∨]-introₗ a≤b
      ... | [∨]-introᵣ a≰b = [∨]-introᵣ (sub₂(_≰_)(_>_) ⦃ [≰][>]-sub ⦄ a≰b)

      [≥]-or-[<] : (a ≥ b) ∨ (a < b)
      [≥]-or-[<] {a}{b} with excluded-middle(a ≥ b)
      ... | [∨]-introₗ a≥b = [∨]-introₗ a≥b
      ... | [∨]-introᵣ a≱b = [∨]-introᵣ (sub₂(_≱_)(_<_) ⦃ [≱][<]-sub ⦄ a≱b)

  module ByStrictPartialOrder ([≤]-def-[<][≡] : ∀{a b} → (a ≤ b) ↔ ((a < b) ∨ (a ≡ b))) ⦃ ord : Strict.PartialOrder(_<_) ⦄ where
    open By-[<] [≤]-def-[<][≡]

    open By-[<] [≤]-def-[<][≡] public
      using
      ( [<][≤]-sub
      ; [≡][≤]-sub
      ; [≰][≮]-sub
      ; [≰][≢]-sub
      ; [>][≥]-sub
      ; [≡][≥]-sub
      ; [≱][≯]-sub
      ; [≱][≢]-sub
      ; [<]-def-[≤][≢]ₗ
      ; [≤]-reflexivity
      )

    instance
      [≤]-transitivity : Transitivity(_≤_)
      [≤]-transitivity = [≤]-transitivity-by-trans

    instance
      [≤]-antisymmetry : Antisymmetry(_≤_)(_≡_)
      [≤]-antisymmetry = [≤]-antisymmetry-by-asym

    instance
      [≤]-weakPartialorder : Weak.PartialOrder(_≤_)
      [≤]-weakPartialorder = record{}

    instance
      [<][≱]-sub : ((_<_) ⊆₂ (_≱_))
      [<][≱]-sub = [<][≱]-sub-by-asym

    instance
      [>][≰]-sub : ((_>_) ⊆₂ (_≰_))
      [>][≰]-sub = [>][≰]-sub-by-asym

  module ByStrictTotalOrder ([≤]-def-[<][≡] : ∀{a b} → (a ≤ b) ↔ ((a < b) ∨ (a ≡ b))) ⦃ ord : Strict.TotalOrder(_<_) ⦄ where
    open By-[<] [≤]-def-[<][≡]

    open ByStrictPartialOrder [≤]-def-[<][≡] public

    instance
      [<]-classical : Classical₂(_<_)
      [<]-classical = [<]-classical-by-asym-tri

    instance
      [≤]-classical : Classical₂(_≤_)
      [≤]-classical = [≤]-classical-by-asym-tri

    [≰][≯]-not : (a ≰ b) → (a ≯ b) → ⊥
    [≰][≯]-not = ByReflTriSub.[≰][≯]-not

    [≮][≱]-not : (a ≮ b) → (a ≱ b) → ⊥
    [≮][≱]-not = ByReflTriSub.[≮][≱]-not

    instance
      [≰][>]-sub : (_≰_) ⊆₂ (_>_)
      [≰][>]-sub = ByReflTriSub.[≰][>]-sub

    instance
      [≱][<]-sub : (_≱_) ⊆₂ (_<_)
      [≱][<]-sub = ByReflTriSub.[≱][<]-sub

    instance
      [≯][≤]-sub : (_≯_) ⊆₂ (_≤_)
      [≯][≤]-sub = ByReflTriSub.[≯][≤]-sub

    instance
      [≮][≥]-sub : (_≮_) ⊆₂ (_≥_)
      [≮][≥]-sub = ByReflTriSub.[≮][≥]-sub

    [≤]-or-[>] : (a ≤ b) ∨ (a > b)
    [≤]-or-[>] = ByReflTriSub.[≤]-or-[>]

    [≥]-or-[<] : (a ≥ b) ∨ (a < b)
    [≥]-or-[<] = ByReflTriSub.[≥]-or-[<]
