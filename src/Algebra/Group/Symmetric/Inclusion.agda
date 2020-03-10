{-# OPTIONS --safe --without-K #-}

open import Algebra.Bundles using (Group)

module Algebra.Group.Symmetric.Inclusion {g₁ g₂} (𝓖 : Group g₁ g₂) where

open Group 𝓖

open import Algebra.Group.Symmetric 𝓖
open import Algebra.Group.Symmetric.Equality 𝓖
open import Algebra.Morphism
open import Function.Inverse using (Inverse; _∘_; _InverseOf_)
open import Function.Equality using (_⟶_; Π)
open import Function using (_$_)
open import Relation.Binary using (Setoid)

open Π
open Inverse
open _InverseOf_

open import Relation.Binary.Reasoning.Setoid setoid
open Setoid ≣-setoid renaming (_≈_ to _≣_) hiding (Carrier)


⟦_⟧ : Carrier → Sym
⟦ a ⟧ .to ⟨$⟩ x = a ∙ x
⟦ a ⟧ .to .cong i≈j = ∙-congˡ i≈j
⟦ a ⟧ .from ⟨$⟩ x = a ⁻¹ ∙ x
⟦ a ⟧ .from .cong i≈j = ∙-congˡ i≈j
⟦ a ⟧ .inverse-of .left-inverse-of x = begin
  a ⁻¹ ∙ (a ∙ x) ≈˘⟨ assoc (a ⁻¹) a x     ⟩
  (a ⁻¹ ∙ a) ∙ x ≈⟨  ∙-congʳ $ inverseˡ a ⟩
  ε ∙ x          ≈⟨  identityˡ x          ⟩
  x              ∎
⟦ a ⟧ .inverse-of .right-inverse-of x = begin
  a ∙ (a ⁻¹ ∙ x) ≈˘⟨ assoc a (a ⁻¹) x      ⟩
  (a ∙ a ⁻¹) ∙ x ≈⟨  ∙-congʳ $ inverseʳ a  ⟩
  ε ∙ x          ≈⟨  identityˡ x           ⟩
  x              ∎

open IsGroupMorphism
open IsMonoidMorphism
open IsSemigroupMorphism

⟦⟧-GroupMorphism : ⟦_⟧ Is 𝓖 -Group⟶ SymGroup
⟦⟧-GroupMorphism .mn-homo .sm-homo .⟦⟧-cong g≈h .eq = ∙-cong g≈h
⟦⟧-GroupMorphism .mn-homo .sm-homo .∙-homo g h .eq {x} {y} x≈y = begin
  g ∙ h ∙ x   ≈⟨ ∙-congˡ x≈y ⟩
  g ∙ h ∙ y   ≈⟨ assoc g h y ⟩
  g ∙ (h ∙ y) ∎
⟦⟧-GroupMorphism .mn-homo .ε-homo .eq {x} {y} x≈y = begin
  ε ∙ x ≈⟨ identityˡ x ⟩
  x     ≈⟨ x≈y ⟩
  y     ∎
