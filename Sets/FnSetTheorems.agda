module Sets.FnSetTheorems where

open import Sets.FnSet

[∈]-in-[∪] : ∀{T}{a : T}{S₁ S₂ : FnSet(T)} → (a ∈ S₁) → (a ∈ (S₁ ∪ S₂))
[∈]-in-[∪] proof-a = [∨]-introₗ-[𝑇] proof-a

[∈]-in-[∩] : ∀{T}{a : T}{S₁ S₂ : FnSet(T)} → (a ∈ S₁) → (a ∈ S₂) → (a ∈ (S₁ ∩ S₂))
[∈]-in-[∩] proof-a₁ proof-a₂ = [∧]-intro-[𝑇] proof-a₁ proof-a₂

[∈]-in-[∖] : ∀{T}{a : T}{S₁ S₂ : FnSet(T)} → (a ∈ S₁) → (a ∉ S₂) → (a ∈ (S₁ ∖ S₂))
[∈]-in-[∖] proof-a₁ proof-a₂ = [∧]-intro-[𝑇] proof-a₁ proof-a₂

[∈]-in-[∁] : ∀{T}{a : T}{S : FnSet(T)} → (a ∉ S) → (a ∈ (∁ S))
[∈]-in-[∁] = id
