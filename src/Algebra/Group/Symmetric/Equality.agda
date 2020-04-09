{-# OPTIONS --without-K --safe #-}

open import Algebra.Bundles using (Group)

module Algebra.Group.Symmetric.Equality {g₁ g₂} (𝓖 : Group g₁ g₂) where

open Group hiding (setoid)
open Group 𝓖

open import Algebra.Group.Symmetric 𝓖

open import Algebra.Structures using (IsMagma; IsSemigroup; IsMonoid; IsGroup)
open import Data.Product
open import Function using (_$_;_on_)
open import Function.Equality using (_⇨_;Π;_⟶_) renaming (_∘_ to _*_)
open import Function.Inverse.Strict using (Inverse)
open import Level
open import Relation.Binary using (Setoid; _⇒_)
import Relation.Binary.Reasoning.Setoid as Reasoning

open Π
open Inverse

funcSetoid : Setoid _ _
funcSetoid = setoid ⇨ setoid

open module S = Setoid setoid using ()
open module F = Setoid funcSetoid using () renaming (_≈_ to _≃_)

infix 4 _≣_
record _≣_ (A B : Sym) : Set (g₁ ⊔ g₂) where
  constructor mk≣
  field
    eq : to A ≃ to B

open _≣_ public

≣-setoid : Setoid _ _
≣-setoid = record
  { Carrier = Sym
  ; _≈_ = _≣_
  ; isEquivalence = record
    { refl = λ {x} → mk≣ (F.refl {x = to x})
    ; sym = λ {x} {y} x≣y → mk≣ (F.sym {x = to x} {y = to y} (eq x≣y))
    ; trans = λ {x} {y} {z} x≣y y≣z → mk≣ (F.trans {i = to x} {j = to y} {k = to z} (eq x≣y) (eq y≣z))
    }
  }

open Setoid ≣-setoid hiding (_≈_) renaming (sym to ≣-sym; trans to ≣-trans; refl to ≣-refl) hiding (Carrier) public

open Setoid
open IsMagma hiding (setoid)
open IsSemigroup hiding (setoid)
open IsMonoid hiding (setoid)
open IsGroup hiding (setoid)

∘-isMagma : IsMagma _≣_ _∘_
∘-isMagma .isEquivalence = isEquivalence ≣-setoid
∘-isMagma .∙-cong (mk≣ x≣y) (mk≣ u≣v) .eq x∼y = x≣y (u≣v x∼y)

∘-isSemiGroup : IsSemigroup _≣_ _∘_
∘-isSemiGroup .isMagma = ∘-isMagma
∘-isSemiGroup .assoc h g f .eq x∼y = cong (to h) (cong (to g) (cong (to f) x∼y))

∘-e-isMonoid : IsMonoid _≣_ _∘_ e
∘-e-isMonoid .isSemigroup = ∘-isSemiGroup
∘-e-isMonoid .identity .proj₁ g .eq = cong (to g)
∘-e-isMonoid .identity .proj₂ g .eq = cong (to g)

∘-e-inv-isGroup : IsGroup _≣_ _∘_ e inv
∘-e-inv-isGroup .isMonoid = ∘-e-isMonoid
∘-e-inv-isGroup .inverse .proj₁ g .eq {x} {y} x∼y =
  left-inverse-of g y (to g ⟨$⟩ x) (cong (to g) x∼y)
∘-e-inv-isGroup .inverse .proj₂ g .eq {x} {y} x∼y =
  right-inverse-of g y (from g ⟨$⟩ x) (cong (from g) x∼y)
∘-e-inv-isGroup .⁻¹-cong {f} {g} (mk≣ f≣g) .eq {x} {y} x∼y = begin
  from f ⟨$⟩ x                 ≈˘⟨ left-inverse-of g (from f ⟨$⟩ x) (to g ⟨$⟩ (from f ⟨$⟩ x)) S.refl ⟩
  from g * to g * from f ⟨$⟩ x ≈˘⟨ cong (from g) $ f≣g S.refl ⟩
  from g * to f * from f ⟨$⟩ x ≈⟨ cong (from g) $ right-inverse-of f y (from f ⟨$⟩ x) (cong (from f) x∼y) ⟩
  from g ⟨$⟩ y ∎
  where
    open import Relation.Binary.Reasoning.Setoid setoid

SymGroup : Group (g₁ ⊔ g₂) (g₁ ⊔ g₂)
Carrier SymGroup = Sym
_≈_ SymGroup = _≣_
_∙_ SymGroup = _∘_
ε SymGroup = e
SymGroup ⁻¹ = inv
isGroup SymGroup = ∘-e-inv-isGroup
