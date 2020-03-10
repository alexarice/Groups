{-# OPTIONS --without-K --safe #-}

open import Algebra.Bundles using (Group)
open import Level

module Machinery {g₁ g₂} (G : Group g₁ g₂) where

open Group G

open import Function.Definitions _≈_ _≈_
open import Function.Inverse renaming (sym to inv)
open import Function using (_$_)
open Inverse
open _InverseOf_
open import Function.Endomorphism.Setoid
open import Function.Equality using (_⇨_;Π;_⟶_)
open Π
open import Relation.Binary using (Setoid; _⇒_)
open import Algebra.Definitions hiding (Inverse)

Sym : Set (g₁ ⊔ g₂)
Sym = Inverse setoid setoid


e : Sym
e = id

FuncSetoid : Setoid (g₁ ⊔ g₂) (g₁ ⊔ g₂)
FuncSetoid = setoid ⇨ setoid

open module S = Setoid setoid using ()
open module F = Setoid FuncSetoid using () renaming (_≈_ to _≃_)

record SymEq (f g : Sym) : Set (suc (g₁ ⊔ g₂)) where
  field
    eq : to f ≃ to g

open SymEq

≣-setoid : Setoid (g₁ ⊔ g₂) (suc (g₁ ⊔ g₂))
≣-setoid = record
  { Carrier = Sym
  ; _≈_ = SymEq
  ; isEquivalence = record
    { refl = λ {x} → record { eq = F.refl {to x} }
    ; sym = λ {f g} f≃g → record { eq = F.sym {to f} {to g} (eq f≃g) }
    ; trans = λ {f g h} f≃g g≃h → record { eq = F.trans {to f} {to g} {to h} (eq f≃g) (eq g≃h) }
    }
  }


record PartSymEq (f : Endo setoid) (g : Sym) : Set (suc (g₁ ⊔ g₂)) where
  field
    peq : f ≃ to g

open PartSymEq

≣'-setoid : Setoid (g₁ ⊔ g₂) (suc (g₁ ⊔ g₂))
≣'-setoid = record
  { Carrier = Sym
  ; _≈_ = λ f → PartSymEq (to f)
  ; isEquivalence = record
    { refl = λ {x} → record { peq = F.refl {to x} }
    ; sym = λ {f g} f≃g → record { peq = F.sym {to f} {to g} (peq f≃g) }
    ; trans = λ {f g h} f≃g g≃h → record { peq = F.trans {to f} {to g} {to h} (peq f≃g) (peq g≃h) }
    }
  }

open Setoid ≣-setoid using () renaming (_≈_ to _≣_; trans to ≣-trans)
open Setoid ≣'-setoid using () renaming (_≈_ to _≣'_; trans to ≣'-trans)

∘-congˡ : LeftCongruent _≣'_ _∘_
∘-congˡ {f} p .peq x∼y = cong (to f) (peq p x∼y)

∘-congʳ : RightCongruent _≣'_ _∘_
∘-congʳ {f} p .peq x∼y = peq p (cong (to f) x∼y)

weaken : _≣_ ⇒ _≣'_
weaken x≣y .peq = eq x≣y

applyAt : ∀ f {g} before after → f ≣ g → before ∘ f ∘ after ≣' before ∘ g ∘ after
applyAt f {g} before after p = ∘-congˡ {before} {f ∘ after} {g ∘ after} lem
 where
  lem : f ∘ after ≣' g ∘ after
  lem = ∘-congʳ {after} {f} {g} (weaken p)

applyAtT : ∀ f {g} before after {h}
         → f ≣ g
         → before ∘ g ∘ after ≣' h
         → before ∘ f ∘ after ≣' h
applyAtT f {g} before after p rest = ≣'-trans {before ∘ f ∘ after} {before ∘ g ∘ after} (applyAt f before after p) rest

inv-left : (g : Sym) → inv g ∘ g ≣ e
inv-left g .eq {x} x∼y = S.trans (left-inverse-of g x) x∼y

inv-right : (g : Sym) → g ∘ inv g ≣ e
inv-right g .eq {x} {y} x∼y = S.trans (right-inverse-of g x) x∼y

open import Relation.Binary.Reasoning.Setoid setoid

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

hom : ∀ g h → ⟦ g ⟧ ∘ ⟦ h ⟧ ≣ ⟦ g ∙ h ⟧
hom g h .eq {x} {y} x≃y = begin
  g ∙ (h ∙ x) ≈˘⟨ assoc g h x ⟩
  g ∙ h ∙ x   ≈⟨  ∙-congˡ x≃y ⟩
  g ∙ h ∙ y   ∎
