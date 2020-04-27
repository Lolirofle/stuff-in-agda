{-# OPTIONS --sized-types #-}

module Lang.Size where

-- Some stuff about sizes that seems to :
-- • Types:
--   • SizeU   : Set
--   • Size    : Set
--   • <ˢⁱᶻᵉ_  : Size → Set
--   • 𝐒ˢⁱᶻᵉ   : Size → Size
--   • ∞ˢⁱᶻᵉ   : Size
--   • _⊔ˢⁱᶻᵉ_ : Size → Size → Size
-- • Subtyping           : ∀s₁∀s₂. (s₁: <ˢⁱᶻᵉ s₂) → (s₁: Size)
-- • Almost irreflexivity: ∀(s: Size). (s ≠ ∞ˢⁱᶻᵉ) → ¬(s: <ˢⁱᶻᵉ s)
-- • Transitivity        : ∀s₁∀s₂∀s₃. (s₁: <ˢⁱᶻᵉ s₂) → (s₂: <ˢⁱᶻᵉ s₃) → (s₁: <ˢⁱᶻᵉ s₃)
-- • Successor           : ∀(s: Size). s: <ˢⁱᶻᵉ 𝐒ˢⁱᶻᵉ(s)
-- • Maximum             : ∀(s: Size). s: <ˢⁱᶻᵉ ∞ˢⁱᶻᵉ
-- • Successor of maximum: 𝐒ˢⁱᶻᵉ(∞ˢⁱᶻᵉ) = ∞ˢⁱᶻᵉ
-- • Max function left   : ∀(s₁: Size)∀(s₂: Size)∀(s₃: Size). ((s₁: <ˢⁱᶻᵉ s₃) ∧ (s₂: <ˢⁱᶻᵉ s₃)) → (((s₁ ⊔ˢⁱᶻᵉ s₂)): <ˢⁱᶻᵉ s₃)
-- • Max function right  : ∀(s₁: Size)∀(s₂: Size)∀(s₃: Size). ((s₁: <ˢⁱᶻᵉ s₂) ∨ (s₁: <ˢⁱᶻᵉ s₃)) → (s₁: <ˢⁱᶻᵉ (s₂ ⊔ˢⁱᶻᵉ s₃))
-- • Max of maximum left : ∀(s: Size). s ⊔ˢⁱᶻᵉ ∞ˢⁱᶻᵉ = ∞ˢⁱᶻᵉ
-- • Max of maximum right: ∀(s: Size). ∞ˢⁱᶻᵉ ⊔ˢⁱᶻᵉ s = ∞ˢⁱᶻᵉ
-- TODO: What is SizeU? See https://github.com/agda/agda/blob/cabe234d3c784e20646636ad082cc1e04ddf007b/src/full/Agda/TypeChecking/Rules/Builtin.hs#L294 , https://github.com/agda/agda/blob/1eec63b1c5566b252c0a4a815ce1df99a772c475/src/full/Agda/TypeChecking/Primitive/Base.hs#L134

{-# BUILTIN SIZEUNIV SizeU #-}
{-# BUILTIN SIZE     Size    #-}
{-# BUILTIN SIZELT   <ˢⁱᶻᵉ_  #-}
{-# BUILTIN SIZESUC  𝐒ˢⁱᶻᵉ   #-}
{-# BUILTIN SIZEINF  ∞ˢⁱᶻᵉ   #-}
{-# BUILTIN SIZEMAX  _⊔ˢⁱᶻᵉ_ #-}

{-
private
  module Test where
    open import Relator.Equals

    types-SizeU : Set
    types-SizeU = SizeU

    types-Size : Set
    types-Size = Size

    types-<ˢⁱᶻᵉ : Size → Set
    types-<ˢⁱᶻᵉ = <ˢⁱᶻᵉ_

    types-𝐒ˢⁱᶻᵉ : Size → Size
    types-𝐒ˢⁱᶻᵉ = 𝐒ˢⁱᶻᵉ

    types-∞ˢⁱᶻᵉ : Size
    types-∞ˢⁱᶻᵉ = ∞ˢⁱᶻᵉ

    types-_⊔ˢⁱᶻᵉ_ : Size → Size → Size
    types-_⊔ˢⁱᶻᵉ_ = _⊔ˢⁱᶻᵉ_

    subtyping : ∀{s₂ : Size}{s₁ : <ˢⁱᶻᵉ s₂} → Size
    subtyping {s₁ = s₁} = s₁

    reflexivity-of-maximum : <ˢⁱᶻᵉ ∞ˢⁱᶻᵉ
    reflexivity-of-maximum = ∞ˢⁱᶻᵉ

    transitivity : ∀{s₃ : Size}{s₂ : <ˢⁱᶻᵉ s₃}{s₁ : <ˢⁱᶻᵉ s₂} → (<ˢⁱᶻᵉ s₃)
    transitivity {s₁ = s₁} = s₁

    maximum : ∀{s : Size} → <ˢⁱᶻᵉ ∞ˢⁱᶻᵉ
    maximum{s} = s

    successor-of-maximum : 𝐒ˢⁱᶻᵉ ∞ˢⁱᶻᵉ ≡ ∞ˢⁱᶻᵉ
    successor-of-maximum = [≡]-intro

    max-of-maximumₗ : ∀{s : Size} → (∞ˢⁱᶻᵉ ⊔ˢⁱᶻᵉ s ≡ ∞ˢⁱᶻᵉ)
    max-of-maximumₗ = [≡]-intro

    max-of-maximumᵣ : ∀{s : Size} → (s ⊔ˢⁱᶻᵉ ∞ˢⁱᶻᵉ ≡ ∞ˢⁱᶻᵉ)
    max-of-maximumᵣ = [≡]-intro

    max-function-left : ∀{s₃ : Size}{s₁ : <ˢⁱᶻᵉ s₃}{s₂ : <ˢⁱᶻᵉ s₃} → (<ˢⁱᶻᵉ s₃)
    max-function-left {s₁ = s₁}{s₂ = s₂} = s₁ ⊔ˢⁱᶻᵉ s₂

    max-function-rightₗ : ∀{s₂ s₃ : Size}{s₁ : <ˢⁱᶻᵉ s₂} → (<ˢⁱᶻᵉ (s₂ ⊔ˢⁱᶻᵉ s₃))
    max-function-rightₗ {s₁ = s₁} = s₁

    max-function-rightᵣ : ∀{s₂ s₃ : Size}{s₁ : <ˢⁱᶻᵉ s₃} → (<ˢⁱᶻᵉ (s₂ ⊔ˢⁱᶻᵉ s₃))
    max-function-rightᵣ {s₁ = s₁} = s₁

    -- TODO: Is this supposed to not work? This is: ∀(sₗ₁ : Size)∀(sₗ₂ : Size)∀(sᵣ : Size) → (sₗ₁ <ˢⁱᶻᵉ sₗ₂) → ((sₗ₁ ⊔ˢⁱᶻᵉ sᵣ) <ˢⁱᶻᵉ (sₗ₂ ⊔ˢⁱᶻᵉ sᵣ))
    max-should-work? : ∀{sₗ₂ sᵣ : Size}{sₗ₁ : <ˢⁱᶻᵉ sₗ₂} → (<ˢⁱᶻᵉ (sₗ₂ ⊔ˢⁱᶻᵉ sᵣ))
    max-should-work? {sᵣ = sᵣ}{sₗ₁ = sₗ₁} = sₗ₁ ⊔ˢⁱᶻᵉ sᵣ
-}
