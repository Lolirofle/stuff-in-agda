module Automaton.DeterministicFinite where

import      Level as Lvl
open import Boolean
import      Boolean.Operators
open        Boolean.Operators.Programming
open import Data renaming(_⨯_ to _⨯'_)
open import Functional
open import List renaming (∅ to [])

-- According to http://www.cse.chalmers.se/edu/course/TMV027/lec5.pdf

-- Deterministic Finite Automata
-- `state`        is Q  (the finite set of states)
-- `alphabet`     is ∑  (the finite set of symbols/the alphabet)
-- `transition`   is δ  (the total transition function)
-- `startState`   is q₀ (the start state)
-- `isFinalState` is (x ↦ elem x F) (the function that checks whether a state is a final/accepting state)
record DFA (State : Set) (Alphabet : Set) : Set where
  constructor Dfa
  field
    transition   : State → Alphabet → State
    startState   : State
    isFinalState : State → Bool

  states   = State
  alphabet = Alphabet

  wordTransition : State → List(Alphabet) → State
  wordTransition initialState []            = initialState
  wordTransition initialState (head ⊰ tail) = wordTransition state tail where
    state = transition initialState head

  Q  = State
  ∑  = Alphabet
  δ  = transition
  δ̂  = wordTransition
  q₀ = startState
  F  = isFinalState

  -- If when the input is read from the start state the automaton stops in a final state, it accepts the word.
  isWordAccepted : List(∑) → Bool
  isWordAccepted word = F(δ̂(q₀)(word))

-- Automaton that accepts words accepted by both of the specified automatons
_⨯_ : ∀{Q₁ Q₂}{∑} → DFA(Q₁)(∑) → DFA(Q₂)(∑) → DFA(Q₁ ⨯' Q₂)(∑)
_⨯_ {Q₁}{Q₂}{∑} (Dfa δ₁ q₀₁ F₁) (Dfa δ₂ q₀₂ F₂) = Dfa δ q₀ F where
  δ : (Q₁ ⨯' Q₂) → ∑ → (Q₁ ⨯' Q₂)
  δ(q₀₁ , q₀₂)(word) = (δ₁(q₀₁)(word) , δ₂(q₀₂)(word))

  q₀ : (Q₁ ⨯' Q₂)
  q₀ = (q₀₁ , q₀₂)

  F : (Q₁ ⨯' Q₂) → Bool
  F(q₁ , q₂) = F₁(q₁) && F₂(q₂)

-- Automaton that accepts words accepted by any of the specified automatons
_+_ : ∀{Q₁ Q₂}{∑} → DFA(Q₁)(∑) → DFA(Q₂)(∑) → DFA(Q₁ ⨯' Q₂)(∑)
_+_ {Q₁}{Q₂}{∑} (Dfa δ₁ q₀₁ F₁) (Dfa δ₂ q₀₂ F₂) = Dfa δ q₀ F where
  δ : (Q₁ ⨯' Q₂) → ∑ → (Q₁ ⨯' Q₂)
  δ(q₀₁ , q₀₂)(word) = (δ₁(q₀₁)(word) , δ₂(q₀₂)(word))

  q₀ : (Q₁ ⨯' Q₂)
  q₀ = (q₀₁ , q₀₂)

  F : (Q₁ ⨯' Q₂) → Bool
  F(q₁ , q₂) = F₁(q₁) || F₂(q₂)

-- Automaton that accepts words not accepted by the specified automaton
∁_ : ∀{Q}{∑} → DFA(Q)(∑) → DFA(Q)(∑)
∁_ (Dfa δ q₀ F) = Dfa δ q₀ ((!_) ∘ F)

module Language where
  open import Logic.Propositional{Lvl.𝟎}
  open import Logic.Predicate{Lvl.𝟎}{Lvl.𝟎}
  open import FormalLanguage
  open import Relator.Equals{Lvl.𝟎}{Lvl.𝟎}

  -- The language accepted by a DFA.
  -- This is a linguistic interpretation of an automaton, that it is a grammar of the language.
  -- A language accepts the empty word when the start state is a final state.
  -- The language of a suffix is the transition function applied to the start state.
  𝔏 : ∀{Q}{∑}{s} → DFA(Q)(∑) → Language(∑){s}
  Language.accepts-ε   (𝔏(Dfa δ q₀ F)) = F(q₀)
  Language.suffix-lang (𝔏(Dfa δ q₀ F)) = (c ↦ 𝔏(Dfa δ (δ(q₀)(c)) F))

  -- TODO
  -- RegularLanguage : ∀{∑}{s} → Language(∑){s} → Stmt
  -- RegularLanguage{∑}{s}(L) = ∃(Q ↦ ∃{DFA(Q)(∑)}(auto ↦ (𝔏{Q}{∑}{s}(auto) ≡ L)))

module Theorems where
  open        Language
  open import Logic.Propositional{Lvl.𝟎}
  open import Relator.Equals{Lvl.𝟎}{Lvl.𝟎}
  open import FormalLanguage
  open        FormalLanguage.Oper hiding (∁_)

  -- TODO: Is this wrong?
  -- step-isWordAccepted : ∀{Q}{∑} → (auto : DFA(Q)(∑)) → ∀{c}{w} → DFA.isWordAccepted(auto)(c ⊰ w) ≡ DFA.isWordAccepted(Dfa (DFA.δ auto) (DFA.δ(auto)(DFA.q₀(auto))(c)) (DFA.F auto))(w)
  -- step-isWordAccepted auto {c}{[]} = [≡]-intro
  -- step-isWordAccepted auto {c}{w} = [≡]-with-[ DFA.F(auto) ] [≡]-intro

  Language-isWordAccepted : ∀{Q}{∑} → (auto : DFA(Q)(∑)) → ∀{w} → DFA.isWordAccepted(auto)(w) ≡ w is-in (𝔏(auto))
  Language-isWordAccepted{_}{∑}(auto){w} = List-induction base step {w} where
    base : DFA.isWordAccepted(auto)[] ≡ [] is-in (𝔏(auto))
    base = [≡]-intro

    -- TODO: Prove
    postulate step : ∀(c : ∑)(w : List(∑)) → (DFA.isWordAccepted(auto)(w) ≡ w is-in (𝔏(auto))) → (DFA.isWordAccepted(auto)(c ⊰ w) ≡ (c ⊰ w) is-in (𝔏(auto)))
    -- step(c)(w)(prev) =
  -- Language-isWordAccepted (_)          {[]}    = [≡]-intro
  -- Language-isWordAccepted (Dfa δ q₀ F) {c ⊰ w} = test(Dfa δ q₀ F){c ⊰ w} -- Language-isWordAccepted (Dfa δ (δ(q₀)(c)) F) {w}
    -- DFA.isWordAccepted(auto)(c ⊰ w)
    -- DFA.isWordAccepted(Dfa δ q₀ F)(c ⊰ w)
    -- F(δ̂(q₀)(c ⊰ w))
    -- F(δ̂(δ(q₀)(c))(w))

    -- (c ⊰ w) is-in (𝔏(auto))
    -- (c ⊰ w) is-in (𝔏(Dfa δ q₀ F))
    -- w is-in (Language.suffix-lang(𝔏(Dfa δ q₀ F))(c))
    -- w is-in (𝔏(Dfa δ (δ(q₀)(c)) F))

  module _ {∑} {Q}(auto : DFA(Q)(∑)) where
    δ̂-with-[++] : ∀{q : Q}{w₁ w₂ : Word(∑)} → DFA.δ̂(auto)(q)(w₁ ++ w₂) ≡ DFA.δ̂(auto)(DFA.δ̂(auto)(q)(w₁))(w₂)
    δ̂-with-[++] {_}{[]}         = [≡]-intro
    δ̂-with-[++] {q}{a ⊰ w₁}{w₂} = δ̂-with-[++] {DFA.δ(auto)(q)(a)}{w₁}{w₂}

    δ̂-on-[∁] : ∀{q : Q}{w : Word(∑)} → DFA.δ̂(∁ auto)(q)(w) ≡ DFA.δ̂(auto)(q)(w)
    δ̂-on-[∁] {_}{[]}    = [≡]-intro
    δ̂-on-[∁] {q}{a ⊰ w} = δ̂-on-[∁] {DFA.δ(∁ auto)(q)(a)}{w}

    [∁]-isWordAccepted : ∀{w} → DFA.isWordAccepted(∁ auto)(w) ≡ !(DFA.isWordAccepted(auto)(w))
    [∁]-isWordAccepted {w} = [≡]-with-[ x ↦ !(DFA.F(auto)(x)) ] (δ̂-on-[∁]{DFA.q₀(auto)}{w})

    -- TODO: Prove ∁ postulates regarding languages before accepting them, because the definition of ∁ for languages might be wrong.
    -- [∁]-language : 𝔏(∁ auto) ≡ Oper.∁(𝔏(auto))
    -- [∁]-language = [≡]-intro
      -- testtt : ∀{auto}{q} → Language.accepts-ε(𝔏(∁ auto)) ≡ ! Language.accepts-ε(𝔏(auto))
      -- testtt {_}{_} = [≡]-intro

      -- testtt2 : ∀{auto}{c} → Language.suffix-lang(𝔏(∁ auto))(c) ≡ Oper.∁(Language.suffix-lang(𝔏(auto))(c))
      -- testtt2 : ∀{auto}{c} → Language.suffix-lang(𝔏(∁ auto))(c) ≡ Language.suffix-lang(Oper.∁(𝔏(auto)))(c)
      -- testtt2 : ∀{auto}{c} → Language.suffix-lang(Oper.∁(𝔏(auto)))(c) ≡ Oper.∁(Language.suffix-lang(𝔏(auto))(c))
      -- testtt2 {_}{_} = [≡]-intro

  module _ {∑} {Q}(auto : DFA(Q)(∑)) {Q₂} (auto₂ : DFA(Q₂)(∑)) where
    δ̂-on-[⨯] : ∀{q₁ : Q}{q₂ : Q₂}{w : Word(∑)} → DFA.δ̂(auto ⨯ auto₂)(q₁ , q₂)(w) ≡ (DFA.δ̂(auto)(q₁)(w) , DFA.δ̂(auto₂)(q₂)(w))
    δ̂-on-[⨯] {_}{_}{[]}      = [≡]-intro
    δ̂-on-[⨯] {q₁}{q₂}{a ⊰ w} = δ̂-on-[⨯] {DFA.δ(auto)(q₁)(a)}{DFA.δ(auto₂)(q₂)(a)}{w}

    δ̂-on-[+] : ∀{q₁ : Q}{q₂ : Q₂}{w : Word(∑)} → DFA.δ̂(auto + auto₂)(q₁ , q₂)(w) ≡ (DFA.δ̂(auto)(q₁)(w) , DFA.δ̂(auto₂)(q₂)(w))
    δ̂-on-[+] {_}{_}{[]}      = [≡]-intro
    δ̂-on-[+] {q₁}{q₂}{a ⊰ w} = δ̂-on-[+] {DFA.δ(auto)(q₁)(a)}{DFA.δ(auto₂)(q₂)(a)}{w}

    -- TODO: δ̂-on-[𝁼]

    [⨯]-isWordAccepted : ∀{w} → DFA.isWordAccepted(auto ⨯ auto₂)(w) ≡ DFA.isWordAccepted(auto)(w) && DFA.isWordAccepted(auto₂)(w)
    [⨯]-isWordAccepted {w} = [≡]-with-[ DFA.F(auto ⨯ auto₂) ] (δ̂-on-[⨯]{DFA.q₀(auto)}{DFA.q₀(auto₂)}{w})

    [+]-isWordAccepted : ∀{w} → DFA.isWordAccepted(auto + auto₂)(w) ≡ DFA.isWordAccepted(auto)(w) || DFA.isWordAccepted(auto₂)(w)
    [+]-isWordAccepted {w} = [≡]-with-[ DFA.F(auto + auto₂) ] (δ̂-on-[+]{DFA.q₀(auto)}{DFA.q₀(auto₂)}{w})

    -- TODO: Prove postulates
    postulate [⨯]-language : 𝔏(auto ⨯ auto₂) ≡ 𝔏(auto) ∩ 𝔏(auto₂)
    postulate [+]-language : 𝔏(auto + auto₂) ≡ 𝔏(auto) ∪ 𝔏(auto₂)
