module Numeral.Ordinal where

import      Lvl
open import Numeral.Natural
open import Syntax.Function
open import Type

private variable ℓ : Lvl.Level
private variable T : Type{ℓ}

-- Ordinal numbers up to a certain level as a type.
-- 𝟎 is the zero ordinal, the smallest ordinal number.
-- 𝐒 is the successor ordinal function, the smallest ordinal greater than the given argument.
-- lim is the limit ordinal function, the "limit" of the given sequence. The smallest ordinal greater than all values of the given sequence. Note that this is not the usual definition of a "limit ordinal" because `lim` allows arbitrary sequences, specifically those with a maximum, resulting in an equivalent to the successor ordinal `𝐒` (TODO: If this is the case, then 𝐒 is actually unnecessary? Just define it by (lim ∘ const)?
-- Note: Usually the indexing in a limit ordinal should be the class of ordinals before it, so this definition is probably unable to express all ordinals.
data Ordinal(T : Type{ℓ}) : Type{ℓ} where
  𝟎   : Ordinal(T)
  𝐒   : Ordinal(T) → Ordinal(T)
  lim : (T → Ordinal(T)) → Ordinal(T)

{-
data Ordinal' : (ℓ : Lvl.Level) → Typeω where
  𝟎   : Ordinal'(ℓ)
  𝐒   : Ordinal'(ℓ) → Ordinal'(ℓ)
  lim : (Ordinal'(ℓ) → Ordinal'(Lvl.𝐒(ℓ))) → Ordinal'(Lvl.𝐒(ℓ)) -- When the next ordinal have the current ordinal as its index

data Ordinal(T : Type{ℓ}) : Type{ℓ} where
  𝟎   : Ordinal(T)
  lim : (T → Ordinal(T)) → Ordinal(T) -- 𝐒 is expressable through lim

data Ordinal(T : Type{ℓ}) : Type{ℓ} where
  𝟎   : Ordinal(T)
  𝐒   : Ordinal(T) → Ordinal(T)
  lim : (f : T → Ordinal(T)) → ∃(IncreasingSubsequence(_<_)(f)) → Ordinal(T) -- This excludes the cases where f have a maximum, resulting in no intersection between 𝐒 and lim
-}

_+_ : Ordinal(T) → Ordinal(T) → Ordinal(T)
x + 𝟎     = x
x + 𝐒(y)  = 𝐒(x + y)
x + lim f = lim(y ↦ (x + f(y)))

_⋅_ : Ordinal(T) → Ordinal(T) → Ordinal(T)
x ⋅ 𝟎      = 𝟎
x ⋅ 𝐒(y)   = (x ⋅ y) + x
x ⋅ lim f  = lim(y ↦ (x ⋅ f(y)))

_^_ : Ordinal(T) → Ordinal(T) → Ordinal(T)
x ^ 𝟎     = x
x ^ 𝐒(y)  = (x ^ y) ⋅ x
x ^ lim f = lim(y ↦ (x ^ f(y)))

open import Logic.Propositional

private variable x y z x₁ x₂ y₁ y₂ z₁ z₂ : Ordinal(T)

module _ {T : Type{ℓ}} where
  open import Functional
  open import Logic.Propositional

  -- TODO: Not sure if this is correct
  data _<_ : Ordinal(T) → Ordinal(T) → Type{ℓ} where
    minimal : ∀{x} → (𝟎 < 𝐒(x))
    step    : ∀{x y} → (x < y) → (𝐒(x) < 𝐒(y))
    limitₗ  : ∀{f}{x} → (∀{i} → (f(i) < x)) → (lim f < 𝐒(x))
    limitᵣ  : ∀{i}{f}{x} → (x < 𝐒(f(i))) → (x < lim f)

  _>_ = swap(_<_)

  _≤_ : Ordinal(T) → Ordinal(T) → Type
  x ≤ y = x < 𝐒(y)

  _≥_ = swap(_≤_)

  _≡_ : Ordinal(T) → Ordinal(T) → Type
  x ≡ y = (y ≤ x) ∧ (x ≤ y)

  open import Numeral.Natural.Induction
  from-ℕ : ℕ → Ordinal(T)
  from-ℕ = ℕ-elim 𝟎 (const 𝐒)

  _+ₙ_ : Ordinal(T) → ℕ → Ordinal(T)
  _+ₙ_ x = ℕ-elim x (const 𝐒)

  private variable f g : T → Ordinal(T)
  private variable n : T

  [<]-limitₗ-inv : (lim f < 𝐒(x)) → (∀{n} → (f(n) < x))
  [<]-limitₗ-inv (limitₗ p) = p

  open import Logic.Predicate
  open import Type.Properties.Inhabited
  [<]-limitᵣ-inv : (x < lim f) → ∃(n ↦ (x < 𝐒(f(n))))
  [<]-limitᵣ-inv (limitᵣ{n} p) = [∃]-intro n ⦃ p ⦄

  [<]-lim-minimal : ⦃ ◊ T ⦄ → (𝟎 < lim f)
  [<]-lim-minimal = limitᵣ{i = [◊]-existence} minimal

  [<]-lim-maximum : (f(n) < lim f)
  [<]-of-step : (x < 𝐒(x))

  [<]-lim-maximum{f}{n} = limitᵣ{n} [<]-of-step

  [<]-without-step : (𝐒(x) < 𝐒(y)) → (x < y)
  [<]-without-step (step p) = p

  [<]-of-step {𝟎}     = minimal
  [<]-of-step {𝐒(x)}  = step [<]-of-step
  [<]-of-step {lim f} = limitₗ [<]-lim-maximum

  [<]-transitivity : (x < y) → (y < z) → (x < z)
  [<]-transitivity minimal     (step yz)          = minimal
  [<]-transitivity minimal     (limitᵣ {n}{f} yz) = limitᵣ {n}{f} minimal
  [<]-transitivity (step xy)   (step yz)          = step ([<]-transitivity xy yz)
  [<]-transitivity (step xy)   (limitᵣ yz)        = limitᵣ ([<]-transitivity (step xy) yz)
  [<]-transitivity (limitₗ xy) (step yz)          = limitₗ ([<]-transitivity xy yz)
  [<]-transitivity (limitₗ xy) (limitᵣ yz)        = limitᵣ (limitₗ ([<]-without-step([<]-transitivity (step xy) yz)))
  [<]-transitivity (limitᵣ xy) (limitₗ yz)        = [<]-transitivity xy (step yz)
  [<]-transitivity (limitᵣ xy) (limitᵣ yz)        = limitᵣ ([<]-transitivity (limitᵣ xy) yz)

  [<]-stepᵣ : (x < y) → (x < 𝐒(y))
  [<]-stepᵣ minimal    = minimal
  [<]-stepᵣ (step p)   = step ([<]-stepᵣ p)
  [<]-stepᵣ (limitₗ p) = limitₗ ([<]-stepᵣ p)
  [<]-stepᵣ (limitᵣ p) = [<]-transitivity p (step [<]-lim-maximum)

  [<]-to-[≤] : (x < y) → (x ≤ y)
  [<]-to-[≤] = [<]-stepᵣ

  [<]-irreflexivity : ¬(x < x)
  [<]-irreflexivity (step p)            = [<]-irreflexivity p
  [<]-irreflexivity (limitᵣ (limitₗ x)) = [<]-irreflexivity x

  [<]-asymmetry : (x < y) → (y < x) → ⊥
  [<]-asymmetry xy yx = [<]-irreflexivity([<]-transitivity xy yx)

  [<]-without-stepₗ : (𝐒(x) < y) → (x < y)
  [<]-without-stepₗ (step p)   = [<]-stepᵣ p
  [<]-without-stepₗ (limitᵣ p) = limitᵣ ([<]-without-stepₗ p)

  [<]-no-less-than-minimum : ¬(x < 𝟎)
  [<]-no-less-than-minimum ()

  [≤]-minimal : (𝟎 ≤ x)
  [≤]-minimal = minimal

  [≤]-step : (x ≤ y) → (𝐒(x) ≤ 𝐒(y))
  [≤]-step = step

  [≤]-reflexivity : (x ≤ x)
  [≤]-reflexivity = [<]-of-step

  [≡]-reflexivity : (x ≡ x)
  [≡]-reflexivity = [∧]-intro [≤]-reflexivity [≤]-reflexivity

  open import Logic.Propositional.Theorems
  [≡]-symmetry : (x ≡ y) → (y ≡ x)
  [≡]-symmetry = [∧]-symmetry

  [≡]-step : (x ≡ y) → (𝐒(x) ≡ 𝐒(y))
  [≡]-step = [∧]-map step step

  open import Relator.Equals renaming (_≡_ to _≡ₑ_)
  [<]-less-than-one : ⦃ ◊ T ⦄ → (x < 𝐒(𝟎)) → (x ≡ₑ 𝟎)
  [<]-less-than-one minimal = [≡]-intro
  [<]-less-than-one (limitₗ p) with () ← p{[◊]-existence}

  [<][≤]-semitransitivityₗ : ⦃ ◊ T ⦄ → (x ≤ y) → (y < z) → (x < z)
  [<][≤]-semitransitivityₗ {_}        {y}        {.(lim _)} xy                 (limitᵣ yz)  = limitᵣ ([<][≤]-semitransitivityₗ xy yz)
  [<][≤]-semitransitivityₗ {.𝟎}       {.𝟎}       {.(𝐒 _)}    minimal            minimal     = minimal
  [<][≤]-semitransitivityₗ {.𝟎}       {.(𝐒 _)}   {.(𝐒 _)}    minimal            (step yz)   = minimal
  [<][≤]-semitransitivityₗ {.𝟎}       {.(lim _)} {.(𝐒 _)}    minimal            (limitₗ x)  = minimal
  [<][≤]-semitransitivityₗ {.(𝐒 _)}   {.(𝐒 _)}   {.(𝐒 _)}    (step xy)          (step yz)   = step ([<][≤]-semitransitivityₗ xy yz)
  [<][≤]-semitransitivityₗ {.(𝐒 _)}   {.(lim _)} {.(𝐒 _)}    (step (limitᵣ xy)) (limitₗ yz) = step ([<][≤]-semitransitivityₗ xy yz)
  [<][≤]-semitransitivityₗ {.(lim _)} {.𝟎}       {.(𝐒 _)}    (limitₗ xy)        minimal     with () ← xy{[◊]-existence}
  [<][≤]-semitransitivityₗ {.(lim _)} {.(𝐒 _)}   {.(𝐒 _)}    (limitₗ xy)        (step yz)   = limitₗ ([<][≤]-semitransitivityₗ xy yz)
  [<][≤]-semitransitivityₗ {.(lim _)} {.(lim _)} {.(𝐒 _)}    (limitₗ xy)        (limitₗ yz) = limitₗ ([<][≤]-semitransitivityₗ ([∃]-proof([<]-limitᵣ-inv xy)) yz)

  [≤]-transitivity : ⦃ ◊ T ⦄ → (x ≤ y) → (y ≤ z) → (x ≤ z)
  [≤]-transitivity = [<][≤]-semitransitivityₗ

  [≡]-transitivity : ⦃ ◊ T ⦄ → (x ≡ y) → (y ≡ z) → (x ≡ z)
  [≡]-transitivity ([∧]-intro yx xy) ([∧]-intro zy yz) = [∧]-intro ([≤]-transitivity zy yx) ([≤]-transitivity xy yz)

  [<][≤]-semitransitivityᵣ : ⦃ ◊ T ⦄ → (x < y) → (y ≤ z) → (x < z)
  [<][≤]-semitransitivityᵣ {.𝟎}       {.(𝐒 𝟎)}       {.(𝐒 _)}   minimal (step minimal)         = minimal
  [<][≤]-semitransitivityᵣ {.𝟎}       {.(𝐒 (𝐒 _))}   {.(𝐒 _)}   minimal (step (step yz))       = minimal
  [<][≤]-semitransitivityᵣ {.𝟎}       {.(𝐒 (lim _))} {.(𝐒 _)}   minimal (step (limitₗ yz))     = minimal
  [<][≤]-semitransitivityᵣ {.𝟎}       {.(𝐒 _)}       {.(lim _)} minimal (step (limitᵣ yz))     = limitᵣ{[◊]-existence} minimal
  [<][≤]-semitransitivityᵣ {.(𝐒 _)}   {.(𝐒 _)}       {𝐒 z}      (step xy) (step yz)            = step ([<][≤]-semitransitivityᵣ xy yz)
  [<][≤]-semitransitivityᵣ {.(𝐒 _)}   {.(𝐒 _)}       {lim z}    (step xy) (step (limitᵣ yz))   = limitᵣ (step ([<][≤]-semitransitivityᵣ xy yz))
  [<][≤]-semitransitivityᵣ {.(lim _)} {.(𝐒 _)}       {𝐒 z}      (limitₗ xy) (step yz)          = limitₗ ([<][≤]-semitransitivityᵣ xy yz)
  [<][≤]-semitransitivityᵣ {.(lim _)} {.(𝐒 _)}       {lim z}    (limitₗ xy) (step (limitᵣ yz)) = limitᵣ ([<][≤]-semitransitivityᵣ (limitₗ xy) (step yz))
  [<][≤]-semitransitivityᵣ {x}        {.(lim _)}     {z}        (limitᵣ xy) (limitₗ yz)        = [<][≤]-semitransitivityᵣ xy (step yz)

  {-
  StrictlyIncreasingSubsequenceExistence : ∀{ℓ}{I : Type{ℓ}} → (I → Ordinal(T)) → Type
  StrictlyIncreasingSubsequenceExistence{I = I} (f) = ∃{Obj = ℕ → I}(g ↦ ∀{n} → (f(g(n)) < f(g(𝐒(n)))))

  -- TODO: Requires some kind of search for T
  StrictlyIncreasingSubsequenceExistence-to-no-maximum : StrictlyIncreasingSubsequenceExistence(f) → ¬ ∃(max ↦ ∀{x} → (f(x) < f(max)))
  StrictlyIncreasingSubsequenceExistence-to-no-maximum ([∃]-intro witness) ([∃]-intro witness₁) = [<]-asymmetry {!!} {!!}
  -}

  {- TODO: Maybe unprovable constructively
  [<]-classical : (x < y) ∨ ¬(x < y)
  [<]-classical {𝟎}     {𝟎}     = [∨]-introᵣ \()
  [<]-classical {𝟎}     {𝐒 y}   = [∨]-introₗ minimal
  [<]-classical {𝟎}     {lim y} = [∨]-introₗ (limitᵣ{𝟎} minimal)
  [<]-classical {𝐒 x}   {𝟎}     = [∨]-introᵣ \()
  [<]-classical {𝐒 x}   {𝐒 y}   = [∨]-elim2 step (_∘ [<]-without-step) ([<]-classical {x} {y})
  [<]-classical {𝐒 x}   {lim y} with [<]-classical {x} {lim y}
  ... | [∨]-introₗ p = {!!}
  ... | [∨]-introᵣ p = {!!}
  [<]-classical {lim x} {𝟎}     = [∨]-introᵣ \()
  [<]-classical {lim x} {𝐒 y}   with [<]-classical {lim x} {y}
  ... | [∨]-introₗ (limitₗ p)          = [∨]-introₗ (limitₗ ([<]-stepᵣ p))
  ... | [∨]-introₗ (limitᵣ (limitₗ p)) = [∨]-introₗ (limitₗ (limitᵣ ([<]-stepᵣ p)))
  ... | [∨]-introᵣ p = [∨]-introᵣ (p ∘ (q ↦ {![<]-limitₗ-inv q!}))
  [<]-classical {lim x} {lim y} = {!!}
  -}

  {- TODO: This is true when there is no maximum for f
  ∀{x} → ∃(y ↦ (x < y) ∧ (f(x) < f(y)))
  test : (x < lim f) → (𝐒(x) < lim f)
  test {𝟎} (limitᵣ minimal) = limitᵣ (step {!!})
  test {𝐒 x} (limitᵣ (step p)) = limitᵣ (step {!!})
  test {lim x} (limitᵣ (limitₗ x₁)) = {!!}
  -}

  {- TODO: Also unprovable constructively?
  f either have a maximum value or is unbounded (so, this would require some kind of search?)

  [<]-sequence-limit : ∀{n} → (f(n) < lim g) → ((∀{n} → (f(n) < lim g)) ∨ (f(n) ≡ x))


  [≤]-total : ⦃ ◊ T ⦄ → ((x ≤ y) ∨ (y ≤ x))
  [≤]-total {𝟎} {_} = [∨]-introₗ minimal
  [≤]-total {_} {𝟎} = [∨]-introᵣ minimal
  [≤]-total {𝐒 x} {𝐒 y} = [∨]-elim2 step step ([≤]-total {x} {y})
  [≤]-total {𝐒 x} {lim y} with [≤]-total {x} {lim y}
  ... | [∨]-introₗ minimal = [∨]-introₗ (step [<]-lim-minimal)
  ... | [∨]-introₗ (step (limitᵣ p)) = [∨]-introₗ (step (limitᵣ (step {!!})))
  ... | [∨]-introₗ (limitₗ p) = [∨]-introₗ (step (limitᵣ (limitₗ (\{n} → {![<]-limitᵣ-inv (p{n})!}))))
  ... | [∨]-introᵣ p = [∨]-introᵣ ([<]-stepᵣ p)
  [≤]-total {lim x} {𝐒 y} = {!!} -- [∨]-symmetry ([≤]-total {𝐒 y} {lim x})
  [≤]-total {lim x} {lim y} = {!!}
  -}

  {-
  [≤]-to-[<][≡] : ⦃ ◊ T ⦄ → (x ≤ y)  → ((x < y) ∨ (x ≡ y))
  [≤]-to-[<][≡] {𝟎}     {𝟎}     minimal    = [∨]-introᵣ ([∧]-intro minimal minimal)
  [≤]-to-[<][≡] {𝟎}     {𝐒 y}   minimal    = [∨]-introₗ minimal
  [≤]-to-[<][≡] {𝟎}     {lim y} minimal    = [∨]-introₗ [<]-lim-minimal
  [≤]-to-[<][≡] {𝐒 x}   {𝐒 y}   (step p)   = [∨]-elim2 step [≡]-step ([≤]-to-[<][≡] {x}{y} p)
  [≤]-to-[<][≡] {𝐒 x} {lim y} (step (limitᵣ p)) with [≤]-to-[<][≡] p
  ... | [∨]-introₗ pp = [∨]-introₗ (limitᵣ (step pp))
  ... | [∨]-introᵣ ([∧]-intro l r) = {!!}
  -- [∨]-introᵣ ([∧]-intro (limitₗ (\{n} → {!!})) (step (limitᵣ r)))
  -- [∨]-elim2 (limitᵣ ∘ step) (\([∧]-intro l r) → [∧]-intro (limitₗ {![<]-stepᵣ l!}) (step (limitᵣ r))) ([≤]-to-[<][≡] p)
  [≤]-to-[<][≡] {lim x} {𝟎}     (limitₗ p) = [∨]-introᵣ ([∧]-intro minimal (limitₗ p))
  [≤]-to-[<][≡] {lim x} {𝐒 y}   (limitₗ p) = {!!}
  [≤]-to-[<][≡] {lim x} {lim y} (limitₗ p) = {!!}

  [<]-trichotomy : ⦃ ◊ T ⦄ → ((x < y) ∨ (x ≡ y) ∨ (x > y))
  [<]-trichotomy {𝟎}     {𝟎}     = [∨]-introₗ ([∨]-introᵣ [≡]-reflexivity)
  [<]-trichotomy {𝟎}     {𝐒 y}   = [∨]-introₗ ([∨]-introₗ minimal)
  [<]-trichotomy {𝟎}     {lim y} = [∨]-introₗ ([∨]-introₗ [<]-lim-minimal)
  [<]-trichotomy {𝐒 x}   {𝟎}     = [∨]-introᵣ minimal
  [<]-trichotomy {lim x} {𝟎}     = [∨]-introᵣ [<]-lim-minimal
  [<]-trichotomy {𝐒 x}   {𝐒 y}   = [∨]-elim2 ([∨]-elim2 step [≡]-step) step ([<]-trichotomy {x}{y})
  [<]-trichotomy {𝐒 x}   {lim y} with [<]-trichotomy {x} {lim y}
  ... | [∨]-introₗ ([∨]-introᵣ ([∧]-intro p _)) = [∨]-introᵣ p
  ... | [∨]-introᵣ p                            = [∨]-introᵣ ([<]-stepᵣ p)
  ... | [∨]-introₗ ([∨]-introₗ (limitᵣ{n} p))   = {!!}
  [<]-trichotomy {lim x} {𝐒 y}   = {!!}
  [<]-trichotomy {lim x} {lim y} = {!!}
  -}

  lim-of-constant : ⦃ ◊ T ⦄ → (lim(const x) ≡ 𝐒(x))
  lim-of-constant = [∧]-intro (step (limitᵣ{[◊]-existence} [<]-of-step)) (limitₗ [<]-of-step)

  lim-of-sequence-with-maximum : ∀{max} → (∀{n} → (f(n) ≤ f(max))) → (lim f ≡ 𝐒(f(max)))
  lim-of-sequence-with-maximum{max = max} p = [∧]-intro (step (limitᵣ{max} [<]-of-step)) (limitₗ p)

  -- ∃(max ↦ (∀{n} → (f(n) ≤ f(max))) ∧ (lim f ≡ 𝐒(f(max)))) ∨ (∀{x} → (𝐒(f(x)) < lim f)) -- or maybe (∀{x y} → (f(x) + f(y) < lim f))

  lim-[≤]-function : (∀{x} → (f(x) ≤ g(x))) → (lim f ≤ lim g)
  lim-[≤]-function p = limitₗ(limitᵣ p)

  lim-function : (∀{x} → (f(x) ≡ g(x))) → (lim f ≡ lim g)
  lim-function p = [∧]-intro (lim-[≤]-function([∧]-elimₗ p)) (lim-[≤]-function([∧]-elimᵣ p))

  [+]-identityᵣ : ((x + 𝟎) ≡ x)
  [+]-identityᵣ = [≡]-reflexivity

  [+]-identityₗ : ((𝟎 + x) ≡ x)
  [+]-identityₗ {𝟎}     = [+]-identityᵣ
  [+]-identityₗ {𝐒 x}   = [≡]-step ([+]-identityₗ {x})
  [+]-identityₗ {lim x} = lim-function [+]-identityₗ

  [+]-associativity : (((x + y) + z) ≡ (x + (y + z)))
  [+]-associativity {x}{y}{𝟎}     = [≡]-reflexivity
  [+]-associativity {x}{y}{𝐒 z}   = [≡]-step ([+]-associativity {x}{y}{z})
  [+]-associativity {x}{y}{lim z} = lim-function ([+]-associativity {x}{y}{_})

  [+]ₗ-[<][≤]-semifunction : (x < y) → ((x + z) ≤ (y + z))
  [+]ₗ-[<][≤]-semifunction {z = 𝟎}     p = [<]-to-[≤] p
  [+]ₗ-[<][≤]-semifunction {z = 𝐒 z}   p = [≤]-step([+]ₗ-[<][≤]-semifunction {z = z} p)
  [+]ₗ-[<][≤]-semifunction {z = lim x} p = limitₗ (limitᵣ ([+]ₗ-[<][≤]-semifunction p))

  [+]ᵣ-[<]-function : ⦃ ◊ T ⦄ → (y < z) → ((x + y) < (x + z))
  [+]ᵣ-[<]-function (minimal {𝟎})     = [<]-of-step
  [+]ᵣ-[<]-function (minimal {𝐒 x})   = [<]-stepᵣ ([+]ᵣ-[<]-function minimal)
  [+]ᵣ-[<]-function (minimal {lim x}) = [<]-stepᵣ (limitᵣ{[◊]-existence} ([+]ᵣ-[<]-function minimal))
  [+]ᵣ-[<]-function (step p)   = step ([+]ᵣ-[<]-function p)
  [+]ᵣ-[<]-function (limitₗ p) = limitₗ ([+]ᵣ-[<]-function p)
  [+]ᵣ-[<]-function (limitᵣ p) = limitᵣ ([+]ᵣ-[<]-function p)

  {-
  [+]-operator : ⦃ ◊ T ⦄ → (x₁ ≡ x₂) → (y₁ ≡ y₂) → ((x₁ + y₁) ≡ (x₂ + y₂))
  [+]-operator ([∧]-intro pxl pxr) ([∧]-intro pyl pyr) = [∧]-intro {!!} {!!} where
    l : (x₁ ≡ x₂) → ((x₁ + y) ≡ (x₂ + y))
    l {𝟎}      {x₂} ([∧]-intro pl pr) = [∧]-intro {!!} {!!}
    l {𝐒 x₁}   {x₂} ([∧]-intro pl pr) = [∧]-intro {!!} {!!}
    l {lim x₁} {x₂} ([∧]-intro pl pr) = [∧]-intro {!!} {!!}

    r : (y₁ ≡ y₂) → ((x + y₁) ≡ (x + y₂))
    r ([∧]-intro pl pr) = [∧]-intro ([+]ᵣ-[<]-function pl) ([+]ᵣ-[<]-function pr)
  -}

  open import Structure.Relator.Ordering
  open        Structure.Relator.Ordering.Strict.Properties using (intro)

  Ordinal-accessibleₗ : ⦃ ◊ T ⦄ → Strict.Properties.Accessibleₗ(_<_)(x)
  Ordinal-accessibleₗ {n} = intro ⦃ proof{n} ⦄ where
    proof : ∀{y x} → ⦃ _ : (x < y) ⦄ → Strict.Properties.Accessibleₗ(_<_)(x)
    proof {_}        {𝟎}                          = intro ⦃ \ ⦃ ⦄ ⦄
    proof {𝐒 𝟎}      {lim y} ⦃ limitₗ p ⦄         with () ← p{[◊]-existence}
    proof {𝐒 x}      {𝐒 y}   ⦃ step p ⦄           = intro ⦃ \{z} ⦃ pz ⦄ → Strict.Properties.Accessibleₗ.proof (Ordinal-accessibleₗ {x}) ⦃ [<][≤]-semitransitivityₗ pz p ⦄ ⦄
    proof {𝐒(𝐒 x)}   {lim y} ⦃ limitₗ p ⦄         = intro ⦃ \{z} ⦃ pz ⦄ → Strict.Properties.Accessibleₗ.proof (Ordinal-accessibleₗ {𝐒 x}) ⦃ [<][≤]-semitransitivityₗ ([∃]-proof([<]-limitᵣ-inv pz)) p ⦄ ⦄
    proof {𝐒(lim x)} {lim y} ⦃ limitₗ p ⦄         = intro ⦃ \{z} ⦃ pz ⦄ → Strict.Properties.Accessibleₗ.proof (Ordinal-accessibleₗ {lim x}) ⦃ [<][≤]-semitransitivityₗ ([∃]-proof([<]-limitᵣ-inv pz)) p ⦄ ⦄
    proof {lim x}    {𝐒 y}   ⦃ limitᵣ(step p) ⦄   = intro ⦃ \{z} ⦃ pz ⦄ → Strict.Properties.Accessibleₗ.proof Ordinal-accessibleₗ ⦃ [<][≤]-semitransitivityₗ pz p ⦄ ⦄
    proof {lim x}    {lim y} ⦃ limitᵣ(limitₗ p) ⦄ = intro ⦃ \{z} ⦃ pz ⦄ → Strict.Properties.Accessibleₗ.proof Ordinal-accessibleₗ ⦃ [<][≤]-semitransitivityₗ ([∃]-proof([<]-limitᵣ-inv pz)) p ⦄ ⦄

module _ where
  open import Functional
  open import Function.Iteration
  open import Numeral.Natural.Induction

  private variable n : ℕ

  _⋅ₙ_ : Ordinal(ℕ) → ℕ → Ordinal(ℕ)
  _⋅ₙ_ x = ℕ-elim 𝟎 (const(lim ∘ (_+ₙ_)))

  ω : Ordinal(ℕ)
  ω = lim from-ℕ

  ω² : Ordinal(ℕ)
  ω² = lim(ω ⋅ₙ_)

  ω-[<]-correctness : from-ℕ(n) < ω
  ω-[<]-correctness {𝟎}    = limitᵣ{i = 𝟎}    minimal
  ω-[<]-correctness {𝐒(n)} = limitᵣ{i = 𝐒(n)} (step [<]-of-step)

  open import Relator.Equals renaming (_≡_ to _≡ₑ_)
  open import Relator.Equals.Proofs
  open import Type.Properties.Inhabited
  open import Structure.Relator

  private variable f : ℕ → Ordinal(ℕ)

  instance
    ℕ-inhabited : ◊ ℕ
    ℕ-inhabited = intro ⦃ 𝟎 ⦄

  strictly-increasing-sequence-when-zero : (∀{n} → (f(n) < f(𝐒(n)))) → (f(n) ≡ₑ 𝟎) → (n ≡ₑ 𝟎)
  strictly-increasing-sequence-when-zero {f = f}{n = 𝟎} ord p = [≡]-intro
  strictly-increasing-sequence-when-zero {f = f}{n = 𝐒 n} ord p with f(n) | ord{n}
  ... | 𝟎     | ord' with () ← [<]-irreflexivity (substitute₂ᵣ(_<_) p ord')
  ... | 𝐒 fn  | ord' with () ← [<]-asymmetry minimal (substitute₂ᵣ(_<_) p ord')
  ... | lim x | ord' with () ← [<]-asymmetry [<]-lim-minimal (substitute₂ᵣ(_<_) p ord')
