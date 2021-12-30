{-# OPTIONS --sized-types #-}

module Automaton.Deterministic.FormalLanguage where

open import Automaton.Deterministic.Finite
open import Automaton.Deterministic
open import Data.Boolean
import      Data.Boolean.Operators
open        Data.Boolean.Operators.Programming
open import Data.List renaming (∅ to [])
open import Functional
import      Lvl
open import Type
open import Type.Size.Finite

private variable ℓ ℓ₁ ℓ₂ ℓₚ : Lvl.Level
private variable Q Q₁ Q₂ State : Type{ℓ}
private variable Σ Σ₁ Σ₂ Alphabet : Type{ℓ}


module Language where
  open import Logic.Propositional
  open import Logic.Predicate
  open import FormalLanguage
  open import FormalLanguage.Equals
  open import Relator.Equals
  open import Relator.Equals.Proofs
  import      Type.Dependent as Type

  -- The language accepted by a DFA.
  -- This is a linguistic interpretation of an automaton, that it is a grammar of the language.
  -- A language accepts the empty word when the start state is a final state.
  -- The language of a suffix is the transition function applied to the start state.
  𝔏 : ∀{s} → DFA{ℓₚ = ℓₚ}(Q)(Σ) → Language(Σ){s}
  Language.accepts-ε   (𝔏(d))   = DFA.isFinal d (DFA.start d)
  Language.suffix-lang (𝔏(d)) c = 𝔏(DFA.transitionedAutomaton d c)

  RegularLanguage : ∀{s}{ℓₚ ℓₑ₁} → Language(Σ) → Type
  RegularLanguage{Σ = Σ}{s = s}{ℓₚ = ℓₚ}{ℓₑ₁ = ℓₑ₁} L = ∃{Obj = Type.Σ(Type{ℓₑ₁})(Q ↦ DFA{ℓₚ = ℓₚ}(Q)(Σ))}(\(Type.intro _ auto) → (𝔏(auto) ≅[ s ]≅ L))

module Proofs where
  open        Language
  open import Logic.Propositional
  open import Relator.Equals
  open import Relator.Equals.Proofs
  open import FormalLanguage
  open        FormalLanguage.Oper hiding (∁_)
  open import Syntax.Transitivity

  -- TODO: Is this wrong?
  -- step-isWordAccepted : ∀{Q}{Σ} → (auto : DFA(Q)(Σ)) → ∀{c}{w} → DFA.isWordAccepted(auto)(c ⊰ w) ≡ DFA.isWordAccepted(Dfa (DFA.δ auto) (DFA.δ(auto)(DFA.q₀(auto))(c)) (DFA.F auto))(w)
  -- step-isWordAccepted auto {c}{[]} = [≡]-intro
  -- step-isWordAccepted auto {c}{w} = congruence₁(DFA.F(auto)) [≡]-intro

  Language-isWordAccepted : ∀{Q}{Σ} → (auto : DFA(Q)(Σ)) → ∀{w} → ({!DFA.isWordAccepted auto w!} ≡ (w ∈? 𝔏(auto)))

  {-
  Language-isWordAccepted : ∀{Q}{Σ} → (auto : DFA(Q)(Σ)) → ∀{w} → (DFA.isWordAccepted(auto)(w) ≡ w ∈? 𝔏(auto))
  Language-isWordAccepted auto {[]}    = [≡]-intro
  Language-isWordAccepted auto {x ⊰ w} =
    DFA.isWordAccepted(auto)(x ⊰ w)                    🝖[ _≡_ ]-[]
    δ̂(q₀)(x ⊰ w) ∈ F                                   🝖[ _≡_ ]-[]
    δ̂(δ(q₀) x) w ∈ F                                   🝖[ _≡_ ]-[ {!Language-isWordAccepted (transitionedAutomaton auto x) {w}!} ]
    DFA.isWordAccepted(transitionedAutomaton auto x) w 🝖[ _≡_ ]-[ Language-isWordAccepted (transitionedAutomaton auto x) {w} ]
    w ∈? Language.suffix-lang(𝔏(auto))(x)              🝖[ _≡_ ]-[] 
    (x ⊰ w) ∈? 𝔏(auto)                                 🝖-end
    where
      open DFA(auto)
      open LetterNotation
  -- congruence₁ {!DFA.F(auto)!} (Language-isWordAccepted {Σ = Σ} auto {w})
  -}

  -- Language-isWordAccepted (_)          {[]}    = [≡]-intro
  -- Language-isWordAccepted (Dfa δ q₀ F) {c ⊰ w} = test(Dfa δ q₀ F){c ⊰ w} -- Language-isWordAccepted (Dfa δ (δ(q₀)(c)) F) {w}
    -- DFA.isWordAccepted(auto)(c ⊰ w)
    -- DFA.isWordAccepted(Dfa δ q₀ F)(c ⊰ w)
    -- F(δ̂(q₀)(c ⊰ w))
    -- F(δ̂(δ(q₀)(c))(w))

    -- (c ⊰ w) ∈? (𝔏(auto))
    -- (c ⊰ w) ∈? (𝔏(Dfa δ q₀ F))
    -- w ∈? (Language.suffix-lang(𝔏(Dfa δ q₀ F))(c))
    -- w ∈? (𝔏(Dfa δ (δ(q₀)(c)) F))
{-
  module _ (auto : Deterministic(Q)(Σ)) where
    δ̂-with-[++] : ∀{q : Q}{w₁ w₂ : Word(Σ)} → Deterministic.δ̂(auto)(q)(w₁ ++ w₂) ≡ DFA.δ̂(auto)(DFA.δ̂(auto)(q)(w₁))(w₂)
    δ̂-with-[++] {_}{[]}         = [≡]-intro
    δ̂-with-[++] {q}{a ⊰ w₁}{w₂} = δ̂-with-[++] {Deterministic.δ(auto)(q)(a)}{w₁}{w₂}

    [∁]-δ̂ : ∀{q : Q}{w : Word(Σ)} → DFA.δ̂(∁ auto)(q)(w) ≡ DFA.δ̂(auto)(q)(w)
    [∁]-δ̂ {_}{[]}    = [≡]-intro
    [∁]-δ̂ {q}{a ⊰ w} = [∁]-δ̂ {DFA.δ(∁ auto)(q)(a)}{w}

    [∁]-isWordAccepted : ∀{w} → DFA.isWordAccepted(∁ auto)(w) ≡ !(DFA.isWordAccepted(auto)(w))
    [∁]-isWordAccepted {w} = congruence₁(x ↦ !(DFA.F(auto)(x))) ([∁]-δ̂{DFA.q₀(auto)}{w})

    -- TODO: Prove ∁ postulates regarding languages before accepting them, because the definition of ∁ for languages might be wrong.
    -- [∁]-language : 𝔏(∁ auto) ≡ Oper.∁(𝔏(auto))
    -- [∁]-language = proof(auto) where
    --   proof : (auto : DFA(Q)(Σ)) → 𝔏(∁ auto) ≡ Oper.∁(𝔏(auto))
    --   proof(Dfa δ q₀ F) = [≡]-substitutionₗ {Lvl.𝟎}{Lvl.𝐒(Lvl.𝟎)} [∁]-language {expr ↦ Lang (! F(q₀)) (c ↦ expr(c))} ([≡]-intro {Lvl.𝟎}{Lvl.𝐒(Lvl.𝟎)})
      -- [≡]-substitution-fnₗ : ∀{T₁ T₂}{x y : T₁ → T₂} → ((c : T₁) → (x(c) ≡ y(c))) → ∀{f : (T₁ → T₂) → TypeN{ℓ₃}} → f(x) ← f(y)
      -- [≡]-substitution-fnₗ [≡]-intro = id?

      -- 𝔏(∁(Dfa δ q₀ F))
      -- = 𝔏(Dfa δ q₀ ((!_) ∘ F))
      -- = Lang ((!_) ∘ F)(q₀)) (c ↦ 𝔏(Dfa δ (δ(q₀)(c)) ((!_) ∘ F)))

      -- Oper.∁(𝔏(Dfa δ q₀ F))
      -- = Lang (! F(q₀)) (c ↦ ∁(𝔏(Dfa δ (δ(q₀)(c)) F)))
      -- = ?

    -- testtt : ∀{auto} → Language.accepts-ε(𝔏{Q}{Σ}(∁ auto)) ≡ ! Language.accepts-ε(𝔏(auto))
    -- testtt : ∀{auto} → Language.accepts-ε(𝔏{Q}{Σ}(∁ auto)) ≡ Language.accepts-ε(Oper.∁ 𝔏(auto))
    -- testtt {_} = [≡]-intro

    -- testtt2 : ∀{auto}{c} → Language.suffix-lang(𝔏(∁ auto))(c) ≡ Oper.∁(Language.suffix-lang(𝔏(auto))(c))
    -- testtt2 : ∀{auto}{c} → Language.suffix-lang(𝔏(∁ auto))(c) ≡ Language.suffix-lang(Oper.∁(𝔏(auto)))(c)
    -- testtt2 : ∀{auto}{c} → Language.suffix-lang(Oper.∁(𝔏{Q}{Σ}(auto)))(c) ≡ Oper.∁(Language.suffix-lang(𝔏(auto))(c))
    -- testtt2 {Dfa δ q₀ F}{_} = [≡]-intro

  module _ (auto : DFA(Q₁)(Σ)) (auto₂ : DFA(Q₂)(Σ)) where
    [⨯]-δ̂ : ∀{q₁ : Q₁}{q₂ : Q₂}{w : Word(Σ)} → DFA.δ̂(auto ⨯ auto₂)(q₁ , q₂)(w) ≡ (DFA.δ̂(auto)(q₁)(w) , DFA.δ̂(auto₂)(q₂)(w))
    [⨯]-δ̂ {_}{_}{[]}      = [≡]-intro
    [⨯]-δ̂ {q₁}{q₂}{a ⊰ w} = [⨯]-δ̂ {DFA.δ(auto)(q₁)(a)}{DFA.δ(auto₂)(q₂)(a)}{w}

    [+]-δ̂ : ∀{q₁ : Q₁}{q₂ : Q₂}{w : Word(Σ)} → DFA.δ̂(auto + auto₂)(q₁ , q₂)(w) ≡ (DFA.δ̂(auto)(q₁)(w) , DFA.δ̂(auto₂)(q₂)(w))
    [+]-δ̂ {_}{_}{[]}      = [≡]-intro
    [+]-δ̂ {q₁}{q₂}{a ⊰ w} = [+]-δ̂ {DFA.δ(auto)(q₁)(a)}{DFA.δ(auto₂)(q₂)(a)}{w}

    -- TODO: δ̂-on-[𝁼]

    [⨯]-isWordAccepted : ∀{w} → DFA.isWordAccepted(auto ⨯ auto₂)(w) ≡ DFA.isWordAccepted(auto)(w) && DFA.isWordAccepted(auto₂)(w)
    [⨯]-isWordAccepted {w} = congruence₁(DFA.F(auto ⨯ auto₂)) ([⨯]-δ̂{DFA.q₀(auto)}{DFA.q₀(auto₂)}{w})

    [+]-isWordAccepted : ∀{w} → DFA.isWordAccepted(auto + auto₂)(w) ≡ DFA.isWordAccepted(auto)(w) || DFA.isWordAccepted(auto₂)(w)
    [+]-isWordAccepted {w} = congruence₁(DFA.F(auto + auto₂)) ([+]-δ̂{DFA.q₀(auto)}{DFA.q₀(auto₂)}{w})

    -- TODO: Prove postulates
    postulate [⨯]-language : 𝔏(auto ⨯ auto₂) ≡ 𝔏(auto) ∩ 𝔏(auto₂)
    postulate [+]-language : 𝔏(auto + auto₂) ≡ 𝔏(auto) ∪ 𝔏(auto₂)
-}
