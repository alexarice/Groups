{-# OPTIONS --safe --without-K #-}

open import Algebra.Bundles using (Group)
module Algebra.Group.Machinery {g₁ g₂} (𝓖 : Group g₁ g₂) where

open import Algebra.Group.Symmetric 𝓖
open import Algebra.Group.Symmetric.Equality 𝓖 renaming (sym to ≣-sym)
open import Algebra.Group.Symmetric.PartialEquality 𝓖 renaming (trans to ≣'-trans)

open Group PartSymGroup

applyAt : ∀ f {g} before after → f ≣ g → before ∘ f ∘ after ≣' before ∘ g ∘ after
applyAt f {g} before after p = ∙-congˡ {before} {f ∘ after} {g ∘ after} lem
 where
  lem : f ∘ after ≣' g ∘ after
  lem = ∙-congʳ {after} {f} {g} (weaken p)

applyAtT : ∀ f {g} before after {h}
         → f ≣ g
         → before ∘ g ∘ after ≣' h
         → before ∘ f ∘ after ≣' h
applyAtT f {g} before after p rest = ≣'-trans {before ∘ f ∘ after} {before ∘ g ∘ after} (applyAt f before after p) rest

applyAtT' : ∀ f {g} before after {h}
          → g ≣ f
          → before ∘ g ∘ after ≣' h
          → before ∘ f ∘ after ≣' h
applyAtT' f before after p rest = applyAtT f before after (≣-sym p) rest

applyAtTnoB : ∀ f {g} after {h}
            → f ≣ g
            → g ∘ after ≣' h
            → f ∘ after ≣' h
applyAtTnoB f after p rest  = applyAtT f e after p rest

applyAtTnoB' : ∀ f {g} after {h}
             → g ≣ f
             → g ∘ after ≣' h
             → f ∘ after ≣' h
applyAtTnoB' f after p rest = applyAtT' f e after p rest

applyAtTnoA : ∀ f {g} before {h}
            → f ≣ g
            → before ∘ g ≣' h
            → before ∘ f ≣' h
applyAtTnoA f before p rest = applyAtT f before e p rest

applyAtTnoA' : ∀ f {g} before {h}
             → g ≣ f
             → before ∘ g ≣' h
             → before ∘ f ≣' h
applyAtTnoA' f before p rest = applyAtT' f before e p rest

applyAtTnoBA : ∀ f {g} {h}
             → f ≣ g
             → g ≣' h
             → f ≣' h
applyAtTnoBA f p rest = applyAtT f e e p rest

applyAtTnoBA' : ∀ f {g} {h}
              → g ≣ f
              → g ≣' h
              → f ≣' h
applyAtTnoBA' f p rest = applyAtT' f e e p rest

applyAtTM : ∀ {g} before after {h}
          → e ≣ g
          → before ∘ g ∘ after ≣' h
          → before ∘ e ∘ after ≣' h
applyAtTM before after p rest = applyAtT e before after p rest

applyAtTM' : ∀ {g} before after {h}
          → g ≣ e
          → before ∘ g ∘ after ≣' h
          → before ∘ after ≣' h
applyAtTM' before after p rest = applyAtTM before after (≣-sym p) rest

applyAtTnoBM : ∀ {g} after {h}
             → e ≣ g
             → g ∘ after ≣' h
             → after ≣' h
applyAtTnoBM after p rest = applyAtTM e after p rest

applyAtTnoBM' : ∀ {g} after {h}
              → g ≣ e
              → g ∘ after ≣' h
              → after ≣' h
applyAtTnoBM' after p rest = applyAtTM' e after p rest

applyAtTnoAM : ∀ {g} before {h}
             → e ≣ g
             → before ∘ g ≣' h
             → before ≣' h
applyAtTnoAM before p rest = applyAtTM before e p rest

applyAtTnoAM' : ∀ {g} before {h}
              → g ≣ e
              → before ∘ g ≣' h
              → before ≣' h
applyAtTnoAM' before p rest = applyAtTM' before e p rest

applyAtTnoBAM : ∀ {g} {h}
              → e ≣ g
              → g ≣' h
              → e ≣' h
applyAtTnoBAM p rest = applyAtTM e e p rest

applyAtTnoBAM' : ∀ {g} {h}
               → g ≣ e
               → g ≣' h
               → e ≣' h
applyAtTnoBAM' p rest = applyAtTM' e e p rest
