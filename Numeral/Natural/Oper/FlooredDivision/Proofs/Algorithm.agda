module Numeral.Natural.Oper.FlooredDivision.Proofs.Algorithm where

import      Lvl
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.FlooredDivision
open import Numeral.Natural.Relation.Order
open import Relator.Equals
open import Relator.Equals.Proofs
open import Syntax.Transitivity

private variable d d₁ d₂ b a' b' : ℕ

inddiv-result-𝐒 : [ 𝐒 d , b ] a' div b' ≡ 𝐒([ d , b ] a' div b')
inddiv-result-𝐒 {d} {b} {𝟎}    {b'}   = [≡]-intro
inddiv-result-𝐒 {d} {b} {𝐒 a'} {𝟎}    = inddiv-result-𝐒 {𝐒 d} {b} {a'} {b}
inddiv-result-𝐒 {d} {b} {𝐒 a'} {𝐒 b'} = inddiv-result-𝐒 {d}{b}{a'}{b'}

inddiv-result : [ d , b ] a' div b' ≡ d + ([ 𝟎 , b ] a' div b')
inddiv-result {𝟎}              = [≡]-intro
inddiv-result {𝐒 d}{b}{a'}{b'} = inddiv-result-𝐒 {d}{b}{a'}{b'} 🝖 [≡]-with(𝐒) (inddiv-result {d}{b}{a'}{b'})

inddiv-of-denominator : [ d , b ] b' div b' ≡ d
inddiv-of-denominator {d} {b} {𝟎}    = [≡]-intro
inddiv-of-denominator {d} {b} {𝐒 b'} = inddiv-of-denominator{d}{b}{b'}

inddiv-of-denominator-successor : [ d , b ] 𝐒 b' div b' ≡ 𝐒 d
inddiv-of-denominator-successor {d} {b} {𝟎}    = [≡]-intro
inddiv-of-denominator-successor {d} {b} {𝐒 b'} = inddiv-of-denominator-successor{d}{b}{b'}

inddiv-step-denominator : [ d , b ] (a' + b') div b' ≡ [ d , b ] a' div 𝟎
inddiv-step-denominator {_} {_} {_}  {𝟎}    = [≡]-intro
inddiv-step-denominator {d} {b} {a'} {𝐒 b'} = inddiv-step-denominator {d} {b} {a'} {b'}

inddiv-lesser : (a' ≤ b') → ([ d , b ] a' div b' ≡ d)
inddiv-lesser min = [≡]-intro
inddiv-lesser {d = d}{b} (succ {𝟎}   {𝟎}    p) = [≡]-intro
inddiv-lesser {d = d}{b} (succ {𝟎}   {𝐒 b'} p) = [≡]-intro
inddiv-lesser {d = d}{b} (succ {𝐒 a'}{𝐒 b'} p) = inddiv-lesser {d = d}{b} p

inddiv-greater : (a' > b') → ([ d , b ] a' div b' ≡ [ 𝐒(d) , b ] (a' −₀ 𝐒(b')) div b)
inddiv-greater {b' = 𝟎}   {d} (succ p) = [≡]-intro
inddiv-greater {b' = 𝐒 b'}{d} (succ p) = inddiv-greater {b' = b'}{d} p
