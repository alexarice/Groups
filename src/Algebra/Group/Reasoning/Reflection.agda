{-# OPTIONS --without-K --safe #-}

open import Algebra.Bundles using (Group)

module Algebra.Group.Reasoning.Reflection {g₁ g₂} (𝓖 : Group g₁ g₂) where

open Group 𝓖

open import Algebra.Group.Symmetric 𝓖
open import Algebra.Group.Symmetric.Equality 𝓖
open import Algebra.Group.Symmetric.Inclusion 𝓖
open import Algebra.Group.Symmetric.PartialEquality 𝓖 using (_≣'_; peq)
open import Algebra.Morphism.Group

open import Function

open import Tactic.Homomorphism.Group public

open import Data.Bool    as Bool    using (Bool; _∨_; if_then_else_)
open import Data.Maybe   as Maybe   using (Maybe; just; nothing; maybe)
open import Data.List    as List    using (List; _∷_; [])
open import Data.Nat     as ℕ       using (ℕ; suc; zero)
open import Data.Product as Product using (_×_; _,_)

open import Agda.Builtin.Reflection
open import Reflection.TCMonadSyntax
open import Reflection.Argument
open import Reflection.Term using (getName; _⋯⟅∷⟆_)

begin-helper : ∀ {g h} → ⟦ g ⟧ ≣ ⟦ h ⟧ → g ≈ h
begin-helper {g} {h} p = ⟦⟧-injective p

begin-helper2 : ∀ {g h} → g ≣' h → g ≣ h
begin-helper2 p .eq = peq p

constructBackSoln : Term → Term → Term → Term → Term
constructBackSoln f eq lhs rhs =
  let domgrp = quote GroupMorphism.from-group ⟨ def ⟩ f ⟨∷⟩ [] in
  let grp = quote GroupMorphism.to-group ⟨ def ⟩ f ⟨∷⟩ [] in
  quote begin-helper ⟨ def ⟩ domgrp ⟨∷⟩
  (quote Group.trans ⟨ def ⟩ grp ⟨∷⟩
    (quote Group.trans ⟨ def ⟩ grp ⟨∷⟩
      (quote proof ⟨ def ⟩ f ⟨∷⟩ buildExpr lhs ⟨∷⟩ [])
      ⟨∷⟩
      (quote begin-helper2 ⟨ def ⟩ domgrp ⟨∷⟩ eq ⟨∷⟩ [])
      ⟨∷⟩ []
    )
    ⟨∷⟩
    (quote Group.sym ⟨ def ⟩ grp ⟨∷⟩
        (quote proof ⟨ def ⟩ f ⟨∷⟩ buildExpr rhs ⟨∷⟩ []) ⟨∷⟩ [])
    ⟨∷⟩
    []) ⟨∷⟩ []


begin-macro : Term → Term → Term → TC _
begin-macro f proof hole = do
  hole' ← inferType hole >>= normalise
  just (lhs , rhs) ← returnTC (getArgs hole')
    where nothing → typeError (termErr hole' ∷ [])
  debugPrint "" 1 (strErr "lhs:" ∷ termErr lhs ∷ strErr "rhs:" ∷ termErr rhs ∷ [])
  let soln = constructBackSoln f proof lhs rhs
  unify hole soln

macro
  begin⟨_⟩_ : Term → Term → Term → TC _
  begin⟨_⟩_ = begin-macro
