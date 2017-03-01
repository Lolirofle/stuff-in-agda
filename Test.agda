module Test where

open import Functional
open import Logic
open import NaturalNumbers

ℕ4IsEven : Even(𝑆(𝑆(𝑆(𝑆(ℕ0)))))
ℕ4IsEven = Even0 ⇒ Even𝑆 ⇒ Even𝑆

ℕ5IsOdd : Odd(𝑆(𝑆(𝑆(𝑆(𝑆(ℕ0))))))
ℕ5IsOdd = Odd0 ⇒ Odd𝑆 ⇒ Odd𝑆

ℕ2Dividesℕ4 : (𝑆(𝑆(ℕ0))) divides (𝑆(𝑆(𝑆(𝑆(ℕ0)))))
ℕ2Dividesℕ4 = Div0 ⇒ Div𝑆 ⇒ Div𝑆

ℕ6IsDivByℕ12 : (𝑆(𝑆(𝑆(𝑆(𝑆(𝑆(ℕ0))))))) divides (𝑆(𝑆(𝑆(𝑆(𝑆(𝑆(𝑆(𝑆(𝑆(𝑆(𝑆(𝑆(ℕ0)))))))))))))
ℕ6IsDivByℕ12 = Div0 ⇒ Div𝑆 ⇒ Div𝑆

ℕ4IsDivByℕ12 : (𝑆(𝑆(𝑆(𝑆(ℕ0))))) divides (𝑆(𝑆(𝑆(𝑆(𝑆(𝑆(𝑆(𝑆(𝑆(𝑆(𝑆(𝑆(ℕ0)))))))))))))
ℕ4IsDivByℕ12 = Div0 ⇒ Div𝑆 ⇒ Div𝑆 ⇒ Div𝑆

ℕ3IsDivByℕ12 : (𝑆(𝑆(𝑆(ℕ0)))) divides (𝑆(𝑆(𝑆(𝑆(𝑆(𝑆(𝑆(𝑆(𝑆(𝑆(𝑆(𝑆(ℕ0)))))))))))))
ℕ3IsDivByℕ12 = Div0 ⇒ Div𝑆 ⇒ Div𝑆 ⇒ Div𝑆 ⇒ Div𝑆

ℕ2IsDivByℕ12 : (𝑆(𝑆(ℕ0))) divides (𝑆(𝑆(𝑆(𝑆(𝑆(𝑆(𝑆(𝑆(𝑆(𝑆(𝑆(𝑆(ℕ0)))))))))))))
ℕ2IsDivByℕ12 = Div0 ⇒ Div𝑆 ⇒ Div𝑆 ⇒ Div𝑆 ⇒ Div𝑆 ⇒ Div𝑆 ⇒ Div𝑆

ℕ1IsDivByℕ12 : (𝑆(ℕ0)) divides (𝑆(𝑆(𝑆(𝑆(𝑆(𝑆(𝑆(𝑆(𝑆(𝑆(𝑆(𝑆(ℕ0)))))))))))))
ℕ1IsDivByℕ12 = Div0 ⇒ Div𝑆 ⇒ Div𝑆 ⇒ Div𝑆 ⇒ Div𝑆 ⇒ Div𝑆 ⇒ Div𝑆 ⇒ Div𝑆 ⇒ Div𝑆 ⇒ Div𝑆 ⇒ Div𝑆 ⇒ Div𝑆 ⇒ Div𝑆
