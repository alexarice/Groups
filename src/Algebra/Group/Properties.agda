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

  inverse-is-unique' : ∀ g h → g ∙ h ≈ ε → g ≈ h ⁻¹
  inverse-is-unique' g h p = begin⟨ ⟦⟧ ⟩
    ⟦ g ⟧ ∘⟨⟩≣˘⟨ invʳ ⟦ h ⟧ ⟩
    ⟨ ⟦ g ⟧ ∘ ⟦ h ⟧ ⟩∘ inv ⟦ h ⟧ ≣⟨ ⟨ ⟦⟧ ⟩⦅ p ⦆ ⟩
    inv ⟦ h ⟧ ∎

  right-cancellation : ∀ g h x → g ∙ x ≈ h ∙ x → g ≈ h
  right-cancellation g h x p = begin⟨ ⟦⟧ ⟩
    ⟦ g ⟧ ∘⟨⟩≣˘⟨ invʳ ⟦ x ⟧ ⟩
    ⟨ ⟦ g ⟧ ∘ ⟦ x ⟧ ⟩∘ inv ⟦ x ⟧ ≣⟨ ⟨ ⟦⟧ ⟩⦅ p ⦆ ⟩
    ⟦ h ⟧ ∘⟨ ⟦ x ⟧ ∘ inv ⟦ x ⟧ ⟩≣⟨ invʳ ⟦ x ⟧ ⟩
    ⟦ h ⟧ ∎

  left-cancellation : ∀ g h x → x ∙ g ≈ x ∙ h → g ≈ h
  left-cancellation g h x p = begin⟨ ⟦⟧ ⟩
    ⟨⟩∘ ⟦ g ⟧ ≣˘⟨ invˡ ⟦ x ⟧ ⟩
    inv ⟦ x ⟧ ∘⟨ ⟦ x ⟧ ∘ ⟦ g ⟧ ⟩≣⟨ ⟨ ⟦⟧ ⟩⦅ p ⦆ ⟩
    ⟨ inv ⟦ x ⟧ ∘ ⟦ x ⟧ ⟩∘ ⟦ h ⟧ ≣⟨ invˡ ⟦ x ⟧ ⟩
    ⟦ h ⟧ ∎

  inv-of-composite : ∀ g h → (g ∙ h) ⁻¹ ≈ h ⁻¹ ∙ g ⁻¹
  inv-of-composite g h = begin⟨ ⟦⟧ ⟩
    inv (⟦ g ⟧ ∘ ⟦ h ⟧) ∘⟨⟩≣˘⟨ invʳ ⟦ g ⟧ ⟩
    inv (⟦ g ⟧ ∘ ⟦ h ⟧) ∘ ⟦ g ⟧ ∘⟨⟩∘ inv ⟦ g ⟧ ≣˘⟨ invʳ ⟦ h ⟧ ⟩
    ⟨ inv (⟦ g ⟧ ∘ ⟦ h ⟧) ∘ (⟦ g ⟧ ∘ ⟦ h ⟧) ⟩∘ inv ⟦ h ⟧ ∘ inv ⟦ g ⟧ ≣⟨ invˡ (⟦ g ⟧ ∘ ⟦ h ⟧) ⟩
    (inv ⟦ h ⟧ ∘ inv ⟦ g ⟧) ∎

  inv-involution : ∀ g → (g ⁻¹) ⁻¹ ≈ g
  inv-involution g = sym (inverse-is-unique (g ⁻¹) g (inverseˡ g))

  inv-e : ε ⁻¹ ≈ ε
  inv-e = sym (inverse-is-unique ε ε (identityˡ ε))
