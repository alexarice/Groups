{-# OPTIONS --safe --without-K #-}

open import Algebra.Bundles using (Group)
module Algebra.Group.Properties {g₁ g₂} (𝓖 : Group g₁ g₂) where

module Part1 {h₁ h₂} (𝓗 : Group h₁ h₂) where

  open Group 𝓗
  open import Algebra.Definitions _≈_

  invˡ : LeftInverse ε _⁻¹ _∙_
  invˡ = inverseˡ

  invʳ : RightInverse ε _⁻¹ _∙_
  invʳ = inverseʳ

module Part2 {h₁ h₂} (𝓗 : Group h₁ h₂) where

  open Group 𝓗
  open import Algebra.Definitions _≈_
  open import Algebra.Group.Symmetric 𝓗
  open import Algebra.Group.Symmetric.Equality 𝓗
  open Part1 SymGroup
  open import Algebra.Group.Reasoning 𝓗

  test : ∀ a b → a ≈ b → ⟦ a ⟧ ≣ ⟦ b ⟧
  test a b p = ⟨ ⟦⟧ ⟩⦅ p ⦆

  test2 : ∀ a b → a ∙ b ≈ b → ⟦ a ⟧ ∘ ⟦ b ⟧ ≣ ⟦ b ⟧
  test2 a b p = ⟨ ⟦⟧ ⟩⦅ p ⦆

  test3 : ∀ x y z → x ∙ (y ⁻¹ ∙ ε) ≈ z ∙ z → ⟦ x ⟧ ∘ (inv ⟦ y ⟧ ∘ e) ≣ ⟦ z ⟧ ∘ ⟦ z ⟧
  test3 x y z p = ⟨ ⟦⟧ ⟩⦅ p ⦆

  identity-is-unique-strong : ∀ a b → a ∙ b ≈ b → a ≈ ε
  identity-is-unique-strong a b p = begin⟨ ⟦⟧ ⟩
    ⟦ a ⟧                     ∘⟨⟩≣˘⟨ invʳ ⟦ b ⟧ ⟩
    ⟨ ⟦ a ⟧ ∘ ⟦ b ⟧ ⟩∘ inv ⟦ b ⟧ ≣⟨ ⟨ ⟦⟧ ⟩⦅ p ⦆ ⟩
    ⟨ ⟦ b ⟧ ∘ inv ⟦ b ⟧         ⟩≣⟨ invʳ ⟦ b ⟧ ⟩
    e                            ∎

  inverse-is-unique : ∀ g h → g ∙ h ≈ ε → h ≈ g ⁻¹
  inverse-is-unique g h p = begin⟨ ⟦⟧ ⟩
    ⟨⟩∘ ⟦ h ⟧                   ≣˘⟨ invˡ ⟦ g ⟧ ⟩
    inv ⟦ g ⟧ ∘⟨ ⟦ g ⟧ ∘ ⟦ h ⟧ ⟩≣⟨ ⟨ ⟦⟧ ⟩⦅ p ⦆ ⟩
    inv ⟦ g ⟧                   ∎
