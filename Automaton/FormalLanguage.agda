{-# OPTIONS --guardedness #-}

module Automaton.FormalLanguage where

open import Automaton
open import Data.Boolean
open import FormalLanguage2
import      Lvl
open import Relator.Equals.Proofs.Equiv
open import Type

private variable ℓ ℓₚ ℓc ℓₑc : Lvl.Level
private variable Σ Input Output : Type{ℓ}

module 𝔏 (A : Automaton Σ Input Bool {ℓc}{ℓₑc}) where
  -- The language accepted by an automaton's configuration.
  -- A language accepts the empty word when the start configuration is a final configuration.
  -- The suffix language is the transition function applied to a configuration.
  config : Automaton.Configuration A → Language(Σ)
  Language.accepts-ε (config(cfg))   = Automaton.output A cfg
  Language.suffix    (config(cfg)) c = config(Automaton.transition A c cfg)

-- The language accepted by an automaton.
-- It is a linguistic interpretation of an automaton that it is the grammar of a language.
𝔏 : Input → Automaton Σ Input Bool {ℓc}{ℓₑc} → Language(Σ)
𝔏 input A = 𝔏.config A (Automaton.initial A input)
