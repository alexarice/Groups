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

  identity-is-unique-strong : ∀ a b → a ∙ b ≈ b → a ≈ ε
  identity-is-unique-strong a b p = begin⟨ ⟦⟧ ⟩
    ⟦ a ⟧ ◂ ⌊⌋                    ≣˘⌊ invʳ ⟦ b ⟧ ⌋
    ⌊ ⟦ a ⟧ ∘ ⟦ b ⟧ ⌋ ▸ inv ⟦ b ⟧ ≣⌊ ⟨ ⟦⟧ ⟩⦅ p ⦆ ⌋
    ⟦ b ⟧ ∘ inv ⟦ b ⟧             ≣⟨ invʳ ⟦ b ⟧ ⟩
    e                             ∎

  inverse-is-unique : ∀ g h → g ∙ h ≈ ε → h ≈ g ⁻¹
  inverse-is-unique g h p = begin⟨ ⟦⟧ ⟩
    ⌊⌋ ▸ ⟦ h ⟧                    ≣˘⌊ invˡ ⟦ g ⟧ ⌋
    inv ⟦ g ⟧ ◂ ⌊ ⟦ g ⟧ ∘ ⟦ h ⟧ ⌋ ≣⌊ ⟨ ⟦⟧ ⟩⦅ p ⦆ ⌋
    inv ⟦ g ⟧                     ∎

  inverse-is-unique' : ∀ g h → g ∙ h ≈ ε → g ≈ h ⁻¹
  inverse-is-unique' g h p = begin⟨ ⟦⟧ ⟩
    ⟦ g ⟧ ◂ ⌊ e ⌋ ≣˘⌊ invʳ ⟦ h ⟧ ⌋
    ⌊ ⟦ g ⟧ ∘ ⟦ h ⟧ ⌋ ▸ inv ⟦ h ⟧ ≣⌊ ⟨ ⟦⟧ ⟩⦅ p ⦆ ⌋
    inv ⟦ h ⟧ ∎

  right-cancellation : ∀ g h x → g ∙ x ≈ h ∙ x → g ≈ h
  right-cancellation g h x p = begin⟨ ⟦⟧ ⟩
    ⟦ g ⟧ ◂ ⌊⌋ ≣˘⌊ invʳ ⟦ x ⟧ ⌋
    ⟦ g ⟧ ∘ ⟦ x ⟧ ∘ inv ⟦ x ⟧ ≡⟨⟩
    ⌊ ⟦ g ⟧ ∘ ⟦ x ⟧ ⌋ ▸ inv ⟦ x ⟧ ≣⌊ ⟨ ⟦⟧ ⟩⦅ p ⦆ ⌋
    ⟦ h ⟧ ◂ ⌊ ⟦ x ⟧ ∘ inv ⟦ x ⟧ ⌋ ≣⌊ invʳ ⟦ x ⟧ ⌋
    ⟦ h ⟧ ∎

  left-cancellation : ∀ g h x → x ∙ g ≈ x ∙ h → g ≈ h
  left-cancellation g h x p = begin⟨ ⟦⟧ ⟩
    ⌊⌋ ▸ ⟦ g ⟧ ≣˘⌊ invˡ ⟦ x ⟧ ⌋
    inv ⟦ x ⟧ ◂ ⌊ ⟦ x ⟧ ∘ ⟦ g ⟧ ⌋ ≣⌊ ⟨ ⟦⟧ ⟩⦅ p ⦆ ⌋
    ⌊ inv ⟦ x ⟧ ∘ ⟦ x ⟧ ⌋ ▸ ⟦ h ⟧  ≣⌊ invˡ ⟦ x ⟧ ⌋
    ⟦ h ⟧ ∎

  inv-of-composite : ∀ g h → (g ∙ h) ⁻¹ ≈ h ⁻¹ ∙ g ⁻¹
  inv-of-composite g h = begin⟨ ⟦⟧ ⟩
    inv (⟦ g ⟧ ∘ ⟦ h ⟧) ◂ ⌊⌋ ≣˘⌊ invʳ ⟦ g ⟧ ⌋
    inv (⟦ g ⟧ ∘ ⟦ h ⟧) ∘ ⟦ g ⟧ ◂ ⌊⌋ ▸ inv ⟦ g ⟧ ≣˘⌊ invʳ ⟦ h ⟧ ⌋
    ⌊ inv (⟦ g ⟧ ∘ ⟦ h ⟧) ∘ (⟦ g ⟧ ∘ ⟦ h ⟧) ⌋ ▸ inv ⟦ h ⟧ ∘ inv ⟦ g ⟧ ≣⌊ invˡ (⟦ g ⟧ ∘ ⟦ h ⟧) ⌋
    (inv ⟦ h ⟧ ∘ inv ⟦ g ⟧) ∎

  inv-involution : ∀ g → (g ⁻¹) ⁻¹ ≈ g
  inv-involution g = sym (inverse-is-unique (g ⁻¹) g (inverseˡ g))

  inv-e : ε ⁻¹ ≈ ε
  inv-e = sym (inverse-is-unique ε ε (identityˡ ε))

module Part3 {h₁ h₂} (𝓗 : Group h₁ h₂) where

  open Group 𝓗
  open import Algebra.Definitions _≈_
  open import Algebra.Group.Symmetric 𝓗
  open import Algebra.Group.Symmetric.Equality 𝓗
  open Part1 SymGroup
  open Part2 SymGroup
  open import Algebra.Group.Reasoning 𝓗

  [_,_] : Carrier → Carrier → Carrier
  [ g , h ] = g ⁻¹ ∙ h ⁻¹ ∙ g ∙ h

  commute-[,]≣e : ∀ g h → g ∙ h ≈ h ∙ g → [ g , h ] ≈ ε
  commute-[,]≣e g h p = begin⟨ ⟦⟧ ⟩
    inv ⟦ g ⟧ ∘ inv ⟦ h ⟧ ◂ ⌊ ⟦ g ⟧ ∘ ⟦ h ⟧ ⌋ ≣⌊ ⟨ ⟦⟧ ⟩⦅ p ⦆ ⌋
    inv ⟦ g ⟧ ◂ ⌊ inv ⟦ h ⟧ ∘ ⟦ h ⟧ ⌋ ▸ ⟦ g ⟧ ≣⌊ invˡ ⟦ h ⟧ ⌋
    inv ⟦ g ⟧ ∘ ⟦ g ⟧ ≣⟨ invˡ ⟦ g ⟧ ⟩
     e ∎

  [,]≣e-commute : ∀ g h → [ g , h ] ≈ ε → g ∙ h ≈ h ∙ g
  [,]≣e-commute g h p = begin⟨ ⟦⟧ ⟩
    ⌊⌋ ▸ ⟦ g ⟧ ∘ ⟦ h ⟧ ≣˘⌊ invʳ ⟦ h ⟧ ⌋
    ⟦ h ⟧ ◂ ⌊⌋ ▸ inv ⟦ h ⟧ ∘ ⟦ g ⟧ ∘ ⟦ h ⟧ ≣˘⌊ invʳ ⟦ g ⟧ ⌋
    ⟦ h ⟧ ∘ ⟦ g ⟧ ◂ ⌊ inv ⟦ g ⟧ ∘ inv ⟦ h ⟧ ∘ ⟦ g ⟧ ∘ ⟦ h ⟧ ⌋ ≣⌊ ⟨ ⟦⟧ ⟩⦅ p ⦆ ⌋
    ⟦ h ⟧ ∘ ⟦ g ⟧ ∎

  inv-[,]-swap : ∀ g h → [ g , h ] ⁻¹ ≈ [ h , g ]
  inv-[,]-swap g h = begin⟨ ⟦⟧ ⟩
    inv (inv ⟦ g ⟧ ∘ inv ⟦ h ⟧ ∘ ⟦ g ⟧ ∘ ⟦ h ⟧) ≣⟨ inv-of-composite (inv ⟦ g ⟧ ∘ inv ⟦ h ⟧ ∘ ⟦ g ⟧) ⟦ h ⟧ ⟩
    inv ⟦ h ⟧ ◂ ⌊ inv (inv ⟦ g ⟧ ∘ inv ⟦ h ⟧ ∘ ⟦ g ⟧) ⌋ ≣⌊ inv-of-composite (inv ⟦ g ⟧ ∘ inv ⟦ h ⟧) ⟦ g ⟧ ⌋
    inv ⟦ h ⟧ ∘ inv ⟦ g ⟧ ◂ ⌊ inv (inv ⟦ g ⟧ ∘ inv ⟦ h ⟧) ⌋ ≣⌊ inv-of-composite (inv ⟦ g ⟧) (inv ⟦ h ⟧) ⌋
    inv ⟦ h ⟧ ∘ inv ⟦ g ⟧ ◂ ⌊ inv (inv ⟦ h ⟧) ⌋ ▸ inv (inv ⟦ g ⟧) ≣⌊ inv-involution ⟦ h ⟧ ⌋
    inv ⟦ h ⟧ ∘ inv ⟦ g ⟧ ∘ ⟦ h ⟧ ◂ ⌊ inv (inv ⟦ g ⟧) ⌋ ≣⌊ inv-involution ⟦ g ⟧ ⌋
    inv ⟦ h ⟧ ∘ inv ⟦ g ⟧ ∘ ⟦ h ⟧ ∘ ⟦ g ⟧ ∎

open Part1 𝓖 public
open Part2 𝓖 public
open Part3 𝓖 public
