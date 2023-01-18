module Formalization.SKICombinatorCalculus where

import      Lvl
import      Function
open import Functional using (_∘_)
open import Type
import      Structure.Relator.Names as Names
open import Structure.Relator.Properties
open import Syntax.Transitivity

data Term : Type{Lvl.𝟎} where
  S   : Term               -- Fusion ([S] f g x = f x (g x))
  K   : Term               -- Constant ([K] x y = x)
  _·_ : Term → Term → Term -- Application ([_·_] f x = f x)
infixl 30 _·_

pattern B  = S · (K · S) · K                 -- Composition ([B] f g x = f(g(x)))
pattern C  = S · (S · (K · B) · S) · (K · K) -- Binary operator argument swap ([C] f x y = f y x). (S · (B · B · S) · (K · K)) also works.
pattern I  = S · K · K                       -- Identity of operation ([I] x = x). (C · K · _) also works, and (W · K).
pattern M  = S · I · I                       -- Self application ([M] f = f f)
pattern W  = S · S · (S · K)                 -- Twice application ([W] f x = f x x)
pattern Ω  = M · M                           -- Term with no normal form after reduction (reduces to itself after three steps)
pattern SW = S · (K · (S · I)) · K           -- Swapped application ([SW] x f = f x)
T = C
Z = B
-- Z = C · (C · (B · N · (S · I · I)) · Ω) · I

{- TODO: Is this possible? Probably, but maybe try to convert to an intermediate data type inbetween, and restrict some of the unallowed combinations that result in infinite types
term-fn-type : ∀{ℓ} → Term → Type{Lvl.𝐒(ℓ)}
term-fn-type {ℓ} S = ∀{X Y Z : Type{ℓ}} → (X → (Y → Z)) → (X → Y) → (X → Z)
term-fn-type {ℓ} K = ∀{X Y : Type{ℓ}} → Y → X → Y
term-fn-type {ℓ} (x · y) = {!term-fn-type {ℓ} x!}
-}

module Derivation where
  data deriv : Term → Type{Lvl.𝟎}

  -- TODO: Is this interpretation incorrect? Maybe L and R is meant to be a term in the middle of any term?
  _⇒_ : Term → Term → Type
  L ⇒ R = ∀{α ι} → deriv(α · L · ι) → deriv(α · R · ι)

  data deriv where
    --term     : ∀{t} → deriv(t)
    constant : ∀{β γ} → ((K · β) · γ) ⇒ β
    fuse     : ∀{β γ δ} → (((S · β) · γ) · δ) ⇒ ((β · δ) · (γ · δ))

  identity : ∀{β} → ((I · β) ⇒ β)
  identity = constant ∘ fuse

  instance
    [⇒]-reflexivity : Reflexivity(_⇒_)
    [⇒]-reflexivity = intro Functional.id

  instance
    [⇒]-transitivity : Transitivity(_⇒_)
    [⇒]-transitivity = intro \xy yz → Functional.swap(Functional._∘_) xy yz

  {-
  composition : ∀{a b c} → (B · a · b · c) ⇒ (a · (b · c))
  composition{a}{b}{c} =
    S · (K · S) · K · a · b · c 🝖[ _⇒_ ]-[ {!!} ]
    a · (b · c)                 🝖[ _⇒_ ]-end
  -}

  {-
  cong : ∀{a b₁ b₂} → (b₁ ⇒ b₂) → ((a · b₁) ⇒ (a · b₂))
  cong {a} {b₁} {b₂} pb (constant d) = {!cong ? d!}
  cong {.(_ · _)} {.(_ · _)} {b₂} pb (fuse d) = {!!}
  -}

  {-
  [·]-function : ∀{a₁ a₂ b₁ b₂} → (a₁ ⇒ a₂) → (b₁ ⇒ b₂) → ((a₁ · b₁) ⇒ (a₂ · b₂))
  [·]-function {a₁} {a₂} {b₁} {b₂} pa pb {α} {ι} (constant {γ = γ} d) = constant([·]-function {K · (a₁ · b₁)}{K · (a₂ · b₂)}{γ}{γ} {![·]-function pa pb!} {!!} d)
  [·]-function {a₁} {a₂} {b₁} {b₂} pa pb {α} {ι} (fuse d) = {!!}
  -}

-- TODO: An inductive definition I came up with. Is it correct? Should be similar to deriv if deriv is correct
-- TODO: (trans (compᵣ p) (compᵣ q)) seem to give the same thing as (compᵣ(trans p q))? Is this alright? It is similar to the relation between cong and trans of Id. Maybe consider splitting appl to compₗ and compᵣ, and then use the reflexive transitive closure because it seems to be equivalent because of that
data _⟶_ : Term → Term → Type{Lvl.𝟎} where
  fuse     : ∀{a b c} → ((((S · a) · b) · c) ⟶ ((a · c) · (b · c)))
  constant : ∀{c t} → (((K · c) · t) ⟶ c)

  appl     : ∀{a₁ a₂ b₁ b₂} → (a₁ ⟶ a₂) → (b₁ ⟶ b₂) → ((a₁ · b₁) ⟶ (a₂ · b₂))
  -- ext      : ∀{f g}{y : Term → Term} → (∀{x} → (g · x) ⟶ y x) → (∀{x} → (f · x) ⟶ y x) → (f ⟶ g)

  refl     : ∀{a} → (a ⟶ a)
  trans    : ∀{a b c} → (a ⟶ b) → (b ⟶ c) → (a ⟶ c)
infixl 29 _⟶_

instance
  [⟶]-reflexivity : Reflexivity(_⟶_)
  [⟶]-reflexivity = intro refl

instance
  [⟶]-transitivity : Transitivity(_⟶_)
  [⟶]-transitivity = intro trans

pattern identityPattern = trans fuse constant

-- 
identity : ∀{t} → ((I · t) ⟶ t)
identity = identityPattern

-- compₗ : ∀{a₁ a₂ b} → (a₁ ⟶ a₂) → ((a₁ · b) ⟶ (a₂ · b))
pattern compₗ p = appl p refl

-- compᵣ : ∀{a b₁ b₂} → (b₁ ⟶ b₂) → ((a · b₁) ⟶ (a · b₂))
pattern compᵣ p = appl refl p

composition : ∀{a b c} → ((B · a · b · c) ⟶ (a · (b · c)))
composition {a}{b}{c} =
  B · a · b · c                     🝖-[ refl ]
  ((S · (K · S) · K · a) · b) · c   🝖-[ compₗ (compₗ fuse) ]
  (((K · S · a) · (K · a)) · b) · c 🝖-[ compₗ (compₗ (compₗ constant)) ]
  ((S · (K · a)) · b) · c           🝖-[ fuse ]
  (K · a · c) · (b · c)             🝖-[ compₗ constant ]
  a · (b · c)                       🝖-end

swap-operator : ∀{a b c} → ((C · a · b · c) ⟶ ((a · c) · b))
swap-operator {a}{b}{c} =
  C · a · b · c                               🝖-[ refl ]
  S · (S · (K · B) · S) · (K · K) · a · b · c 🝖-[ compₗ (compₗ fuse) ]
  (S · (K · B) · S · a) · (K · K · a) · b · c 🝖-[ compₗ (compₗ (appl fuse constant)) ]
  (K · B · a · (S · a)) · K · b · c           🝖-[ compₗ (compₗ (compₗ (compₗ constant))) ]
  B · (S · a) · K · b · c                     🝖-[ compₗ composition ]
  (S · a) · (K · b) · c                       🝖-[ fuse ]
  (a · c) · (K · b · c)                       🝖-[ compᵣ constant ]
  (a · c) · b                                 🝖-end

twice-application : ∀{a b} → ((W · a · b) ⟶ ((a · b) · b))
twice-application{a}{b} =
  S · S · (S · K) · a · b   🝖-[ compₗ fuse ]
  S · a · (S · K · a) · b   🝖-[ fuse ]
  a · b · (S · K · a · b)   🝖-[ compᵣ fuse ]
  a · b · (K · b · (a · b)) 🝖-[ compᵣ constant ]
  a · b · b                 🝖-end

apply-self : ∀{t} → ((M · t) ⟶ (t · t))
apply-self = trans fuse (appl identity identity)

swapped-application : ∀{a b} → ((SW · a · b) ⟶ (b · a))
swapped-application {a}{b} =
  S · (K · (S · I)) · K · a · b   🝖-[ compₗ fuse ]
  (K · (S · I) · a) · (K · a) · b 🝖-[ compₗ (compₗ constant) ]
  (S · I) · (K · a) · b           🝖-[ fuse ]
  I · b · (K · a · b)             🝖-[ appl identity constant ]
  b · a                           🝖-end

-- TODO: This can technically be proven by just `refl`, but the point here is that it is possible for a reduction to be infinite. Use some other operator to express this.
self-reduction : (Ω ⟶ Ω)
self-reduction =
  Ω     🝖-[ refl ]
  M · M 🝖-[ apply-self ]
  M · M 🝖-[ refl ]
  Ω     🝖-end

module Boolean where
  TRUE  = K             -- True
  FALSE = S · K         -- False
  NOT   = FALSE · TRUE  -- Not (Negation)
  OR    = TRUE          -- Or (Disjunction)
  AND   = FALSE         -- And (Conjunction)

  IsTrue : Term → Type{Lvl.𝟎}
  IsTrue(a) = ∀{t f} → ((a · t · f) ⟶ t)

  IsFalse : Term → Type{Lvl.𝟎}
  IsFalse(a) = ∀{t f} → ((a · t · f) ⟶ f)

  reduce-true-is-true : ∀{t} → (t ⟶ TRUE) → IsTrue(t)
  reduce-true-is-true tT = (compₗ (compₗ tT)) 🝖 constant

  reduce-false-is-false : ∀{t} → (t ⟶ FALSE) → IsFalse(t)
  reduce-false-is-false tT = (compₗ (compₗ tT)) 🝖 identityPattern

  true : IsTrue(TRUE)
  true = constant

  false : IsFalse(FALSE)
  false = identityPattern

  not-true-is-false : ∀{t} → IsTrue(t) → IsFalse(t · NOT)
  not-true-is-false {term} t-true {t}{f} =
    term · NOT · t · f 🝖-[ compₗ t-true ]
    NOT · f            🝖-[ fuse ]
    K · f · (TRUE · f) 🝖-[ constant ]
    f                  🝖-end

  {- -- TODO: Not possible?
  not-false-is-true : ∀{t} → IsFalse(t) → IsTrue(t · NOT)
  not-false-is-true {term} t-false {t}{f} =
    term · NOT · t · f         🝖-[ refl ]
    term · (S · K · K) · t · f 🝖-[ {!!} ]
    t                          🝖-end
  -}

  not-true : IsFalse(TRUE · NOT)
  not-true {t}{f} = not-true-is-false constant
    {-TRUE · NOT · t · f            🝖-[ refl ]
    TRUE · (FALSE · TRUE) · t · f 🝖-[ refl ]
    K · (S · K · K) · t · f       🝖-[ compₗ constant ]
    S · K · K · f                 🝖-[ fuse ]
    K · f · (K · f)               🝖-[ constant ]
    f                             🝖-end-}

  {-
  not-false : IsTrue(FALSE · NOT)
  not-false {t}{f} =
    FALSE · NOT · t · f            🝖-[ refl ]
    FALSE · (FALSE · TRUE) · t · f 🝖-[ refl ]
    S · K · (S · K · K) · t · f    🝖-[ compₗ fuse ]
    K · t · (S · K · K · t) · f    🝖-[ compₗ constant ]
    t · f                          🝖-[ {!!} ] -- TODO: ???
    t                              🝖-end
  -- not-false-is-true identity
  -}

  or-true-true : IsTrue(TRUE · OR · TRUE)
  or-true-true = reduce-true-is-true constant

  or-true-false : IsTrue(TRUE · OR · FALSE)
  or-true-false = reduce-true-is-true constant

  or-false-true : IsTrue(FALSE · OR · TRUE)
  or-false-true = reduce-true-is-true(fuse 🝖 constant)

  or-false-false : IsFalse(FALSE · OR · FALSE)
  or-false-false = reduce-false-is-false(fuse 🝖 constant)

  and-true-true : IsTrue(TRUE · TRUE · AND)
  and-true-true = reduce-true-is-true(constant)

  and-true-false : IsFalse(TRUE · FALSE · AND)
  and-true-false = reduce-false-is-false(constant)

  and-false-true : IsFalse(FALSE · TRUE · AND)
  and-false-true = reduce-false-is-false(identity)

  and-false-false : IsFalse(FALSE · FALSE · AND)
  and-false-false = reduce-false-is-false(fuse 🝖 constant)
