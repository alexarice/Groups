{-# OPTIONS --without-K --safe #-}

open import Algebra.Bundles using (Group)

module Algebra.Group.Symmetric.PartialEquality {g₁ g₂} (𝓖 : Group g₁ g₂) where

open Group hiding (setoid)
open Group 𝓖

open import Algebra.Group.Symmetric 𝓖

open import Algebra.Structures using (IsMagma; IsSemigroup; IsMonoid; IsGroup)
open import Data.Product
open import Function using (_$_)
open import Function.Endomorphism.Setoid setoid using (Endo)
open import Function.Equality using (_⇨_;Π;_⟶_) renaming (_∘_ to _*_)
open import Function.Inverse using (Inverse)
open import Level
open import Relation.Binary using (Setoid; _⇒_)

open Π
open Inverse

funcSetoid : Setoid _ _
funcSetoid = setoid ⇨ setoid

open module S = Setoid setoid using ()
open module F = Setoid funcSetoid using () renaming (_≈_ to _≃_)

record PartSymEq (f : Endo) (g : Sym) : Set (suc (g₁ ⊔ g₂)) where
  field
    peq : f ≃ to g

open PartSymEq public

≣'-setoid : Setoid _ _
≣'-setoid = record
  { Carrier = Sym
  ; _≈_ = λ f → PartSymEq (to f)
  ; isEquivalence = record
    { refl = λ {x} → record { peq = F.refl {to x} }
    ; sym = λ {f g} f≃g → record { peq = F.sym {to f} {to g} (peq f≃g) }
    ; trans = λ {f g h} f≃g g≃h → record { peq = F.trans {to f} {to g} {to h} (peq f≃g) (peq g≃h) }
    }
  }

open Setoid ≣'-setoid renaming (_≈_ to _≣'_) public

open Setoid
open IsMagma hiding (setoid)
open IsSemigroup hiding (setoid)
open IsMonoid hiding (setoid)
open IsGroup hiding (setoid)

∘-isMagma : IsMagma _≣'_ _∘_
∘-isMagma .isEquivalence = isEquivalence ≣'-setoid
∘-isMagma .∙-cong  x≣'y u≣'v .peq x∼y = peq x≣'y (peq u≣'v x∼y)

∘-isSemiGroup : IsSemigroup _≣'_ _∘_
∘-isSemiGroup .isMagma = ∘-isMagma
∘-isSemiGroup .assoc h g f .peq x∼y = cong (to h) (cong (to g) (cong (to f) x∼y))

∘-e-isMonoid : IsMonoid _≣'_ _∘_ e
∘-e-isMonoid .isSemigroup = ∘-isSemiGroup
∘-e-isMonoid .identity .proj₁ g .peq = cong (to g)
∘-e-isMonoid .identity .proj₂ g .peq = cong (to g)

∘-e-inv-isGroup : IsGroup _≣'_ _∘_ e inv
∘-e-inv-isGroup .isMonoid = ∘-e-isMonoid
∘-e-inv-isGroup .inverse .proj₁ g .peq {x} x∼y = S.trans (left-inverse-of g x) x∼y
∘-e-inv-isGroup .inverse .proj₂ g .peq {x} x∼y = S.trans (right-inverse-of g x) x∼y
∘-e-inv-isGroup .⁻¹-cong {f} {g} f≣'g .peq {x} {y} x∼y = begin
  from f ⟨$⟩ x                 ≈˘⟨ left-inverse-of g $ from f ⟨$⟩ x ⟩
  from g * to g * from f ⟨$⟩ x ≈˘⟨ cong (from g) $ peq f≣'g S.refl ⟩
  from g * to f * from f ⟨$⟩ x ≈⟨ cong (from g) $ right-inverse-of f x ⟩
  from g ⟨$⟩ x                 ≈⟨ cong (from g) x∼y ⟩
  from g ⟨$⟩ y                 ∎
  where
    open import Relation.Binary.Reasoning.Setoid setoid

PartSymGroup : Group (g₁ ⊔ g₂) (suc (g₁ ⊔ g₂))
Carrier PartSymGroup = Sym
_≈_ PartSymGroup = λ f → PartSymEq (to f)
_∙_ PartSymGroup = _∘_
ε PartSymGroup = e
PartSymGroup ⁻¹ = inv
isGroup PartSymGroup = ∘-e-inv-isGroup

open import Algebra.Group.Symmetric.Equality 𝓖 using (≣-setoid; eq)
open Setoid ≣-setoid renaming (_≈_ to _≣_)

weaken : ∀ {g h} → g ≣ h → g ≣' h
weaken g≣h .peq = eq g≣h
