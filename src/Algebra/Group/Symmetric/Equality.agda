{-# OPTIONS --without-K --safe #-}

open import Algebra.Bundles using (Group)

module Algebra.Group.Symmetric.Equality {g₁ g₂} (𝓖 : Group g₁ g₂) where

open Group hiding (setoid)
open Group 𝓖

open import Algebra.Group.Symmetric.Base 𝓖

open import Algebra.Structures using (IsMagma; IsSemigroup; IsMonoid; IsGroup)
open import Data.Product
open import Function using (_$_)
open import Function.Equality using (_⇨_;Π;_⟶_) renaming (_∘_ to _*_)
open import Function.Inverse using (Inverse;_∘_;id)
open import Level
open import Relation.Binary using (Setoid; _⇒_)

open Π
open Inverse

funcSetoid : Setoid _ _
funcSetoid = setoid ⇨ setoid

open module S = Setoid setoid using ()
open module F = Setoid funcSetoid using () renaming (_≈_ to _≃_)

record SymEq (f g : Sym) : Set (suc (g₁ ⊔ g₂)) where
  field
    eq : to f ≃ to g

open SymEq public

≣-setoid : Setoid _ _
≣-setoid = record
  { Carrier = Sym
  ; _≈_ = SymEq
  ; isEquivalence = record
    { refl = λ {x} → record { eq = F.refl {to x} }
    ; sym = λ {f g} f≃g → record { eq = F.sym {to f} {to g} (eq f≃g) }
    ; trans = λ {f g h} f≃g g≃h → record { eq = F.trans {to f} {to g} {to h} (eq f≃g) (eq g≃h) }
    }
  }

open Setoid ≣-setoid renaming (_≈_ to _≣_)

open Setoid
open IsMagma hiding (setoid)
open IsSemigroup hiding (setoid)
open IsMonoid hiding (setoid)
open IsGroup hiding (setoid)

∘-isMagma : IsMagma _≣_ _∘_
∘-isMagma .isEquivalence = isEquivalence ≣-setoid
∘-isMagma .∙-cong  x≣y u≣v .eq x∼y = eq x≣y (eq u≣v x∼y)

∘-isSemiGroup : IsSemigroup _≣_ _∘_
∘-isSemiGroup .isMagma = ∘-isMagma
∘-isSemiGroup .assoc h g f .eq x∼y = cong (to h) (cong (to g) (cong (to f) x∼y))

∘-id-isMonoid : IsMonoid _≣_ _∘_ id
∘-id-isMonoid .isSemigroup = ∘-isSemiGroup
∘-id-isMonoid .identity .proj₁ g .eq = cong (to g)
∘-id-isMonoid .identity .proj₂ g .eq = cong (to g)

∘-id-inv-isGroup : IsGroup _≣_ _∘_ id inv
∘-id-inv-isGroup .isMonoid = ∘-id-isMonoid
∘-id-inv-isGroup .inverse .proj₁ g .eq {x} x∼y = S.trans (left-inverse-of g x) x∼y
∘-id-inv-isGroup .inverse .proj₂ g .eq {x} x∼y = S.trans (right-inverse-of g x) x∼y
∘-id-inv-isGroup .⁻¹-cong {f} {g} f≣g .eq {x} {y} x∼y = begin
  from f ⟨$⟩ x                 ≈˘⟨ left-inverse-of g $ from f ⟨$⟩ x ⟩
  from g * to g * from f ⟨$⟩ x ≈˘⟨ cong (from g) $ eq f≣g S.refl ⟩
  from g * to f * from f ⟨$⟩ x ≈⟨ cong (from g) $ right-inverse-of f x ⟩
  from g ⟨$⟩ x                 ≈⟨ cong (from g) x∼y ⟩
  from g ⟨$⟩ y                 ∎
  where
    open import Relation.Binary.Reasoning.Setoid setoid

SymGroup : Group (g₁ ⊔ g₂) (suc (g₁ ⊔ g₂))
Carrier SymGroup = Sym
_≈_ SymGroup = _≣_
_∙_ SymGroup = _∘_
ε SymGroup = e
SymGroup ⁻¹ = inv
isGroup SymGroup = ∘-id-inv-isGroup
