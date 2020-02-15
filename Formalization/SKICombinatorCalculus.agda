module Formalization.SKICombinatorCalculus where

import      Lvl
import      Function
open import Type
open import Structure.Relator.Properties
open import Syntax.Transitivity

data Term : Type{Lvl.𝟎} where
  S   : Term               -- Fusion
  K   : Term               -- Constant
  _·_ : Term → Term → Term
infixl 30 _·_

pattern B  = S · (K · S) · K                 -- Composition
pattern C  = S · (S · (K · B) · S) · (K · K) -- Swapped application
pattern I  = S · K · K                       -- Identity of operation
pattern SA = (S · I) · I                     -- Self application
pattern W  = S · S · (S · K)                 --
pattern Ω  = SA · SA                         --
pattern SW = S · (K · (S · I)) · K           -- Swapped operation
T = C
Z = B
-- Z = C · (C · (B · N · (S · I · I)) · Ω) · I

data _⟶_ : Term → Term → Type{Lvl.𝟎} where -- TODO: Use reflexive-transitive closure instead
  constant : ∀{c t} → (((K · c) · t) ⟶ c)
  fuse     : ∀{a b c} → ((((S · a) · b) · c) ⟶ ((a · c) · (b · c)))

  comp     : ∀{a₁ a₂ b₁ b₂} → (a₁ ⟶ a₂) → (b₁ ⟶ b₂) → ((a₁ · b₁) ⟶ (a₂ · b₂))
  refl     : ∀{a} → (a ⟶ a)
  trans    : ∀{a b c} → (a ⟶ b) → (b ⟶ c) → (a ⟶ c)
infixl 29 _⟶_

instance
  [⟶]-reflexivity : Reflexivity(_⟶_)
  [⟶]-reflexivity = intro refl

instance
  [⟶]-transitivity : Transitivity(_⟶_)
  [⟶]-transitivity = intro trans

-- identity : ∀{t} → ((I · t) ⟶ t)
pattern identity = trans fuse constant

-- compₗ : ∀{a₁ a₂ b} → (a₁ ⟶ a₂) → ((a₁ · b) ⟶ (a₂ · b))
pattern compₗ p = comp p refl

-- compᵣ : ∀{a b₁ b₂} → (b₁ ⟶ b₂) → ((a · b₁) ⟶ (a · b₂))
pattern compᵣ p = comp refl p

composition : ∀{a b c} → ((B · a · b · c) ⟶ (a · (b · c)))
composition {a}{b}{c} =
  B · a · b · c                     🝖-[ refl ]
  ((S · (K · S) · K · a) · b) · c   🝖-[ compₗ (compₗ fuse) ]
  (((K · S · a) · (K · a)) · b) · c 🝖-[ compₗ (compₗ (compₗ constant)) ]
  ((S · (K · a)) · b) · c           🝖-[ fuse ]
  (K · a · c) · (b · c)             🝖-[ compₗ constant ]
  a · (b · c)                       🝖-end

swapped-application : ∀{a b c} → ((C · a · b · c) ⟶ ((a · c) · b))
swapped-application {a}{b}{c} =
  C · a · b · c                               🝖-[ refl ]
  S · (S · (K · B) · S) · (K · K) · a · b · c 🝖-[ compₗ (compₗ fuse) ]
  (S · (K · B) · S · a) · (K · K · a) · b · c 🝖-[ compₗ (compₗ (comp fuse constant)) ]
  (K · B · a · (S · a)) · K · b · c           🝖-[ compₗ (compₗ (compₗ (compₗ constant))) ]
  (B · (S · a)) · K · b · c                   🝖-[ compₗ composition ]
  (S · a) · (K · b) · c                       🝖-[ fuse ]
  (a · c) · (K · b · c)                       🝖-[ compᵣ constant ]
  (a · c) · b                                 🝖-end

apply-self : ∀{t} → ((SA · t) ⟶ (t · t))
apply-self = trans fuse (comp identity identity)

swapping : ∀{a b} → ((SW · a · b) ⟶ (b · a))
swapping {a}{b} =
  S · (K · (S · I)) · K · a · b   🝖-[ compₗ fuse ]
  (K · (S · I) · a) · (K · a) · b 🝖-[ compₗ (compₗ constant) ]
  (S · I) · (K · a) · b           🝖-[ fuse ]
  I · b · (K · a · b)             🝖-[ comp identity constant ]
  b · a                           🝖-end

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
  reduce-false-is-false tT = (compₗ (compₗ tT)) 🝖 identity

  true : IsTrue(TRUE)
  true = constant

  false : IsFalse(FALSE)
  false = identity

  not-true-is-false : ∀{t} → IsTrue(t) → IsFalse(t · NOT)
  not-true-is-false t-true = (compₗ t-true) 🝖 fuse 🝖 constant

  {-not-false-is-true : ∀{t} → IsFalse(t) → IsTrue(t · NOT)
  not-false-is-true {term} t-false {t}{f} =
    term · NOT · t · f         🝖-[ refl ]
    term · (S · K · K) · t · f 🝖-[ {!!} ]
    f · (S · K · K) · t · f 🝖-[ {!!} ]
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

  not-false : IsTrue(FALSE · NOT)
  not-false {t}{f} =
    FALSE · NOT · t · f            🝖-[ refl ]
    FALSE · (FALSE · TRUE) · t · f 🝖-[ refl ]
    S · K · (S · K · K) · t · f    🝖-[ compₗ fuse ]
    K · t · (S · K · K · t) · f    🝖-[ compₗ constant ]
    t · f                          🝖-[ {!!} ] -- TODO: ???
    t                              🝖-end
  -- not-false-is-true identity

  or-true-true : IsTrue(TRUE · OR · TRUE)
  or-true-true = reduce-true-is-true constant

  or-true-false : IsTrue(TRUE · OR · FALSE)
  or-true-false = reduce-true-is-true constant

  or-false-true : IsTrue(FALSE · OR · TRUE)
  or-false-true = reduce-true-is-true(fuse 🝖 constant)

  or-false-true2 : IsTrue(FALSE · OR · TRUE)
  or-false-true2 = reduce-true-is-true(fuse 🝖 constant)

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
