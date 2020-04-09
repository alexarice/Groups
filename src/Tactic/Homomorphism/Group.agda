{-# OPTIONS --safe --without-K --no-exact-split #-}

module Tactic.Homomorphism.Group where

open import Algebra.Morphism
open import Algebra.Bundles using (Group)
open import Function
open import Level

open import Data.Bool    as Bool    using (Bool; _∨_; if_then_else_;false)
open import Data.Maybe   as Maybe   using (Maybe; just; nothing; maybe)
open import Data.List    as List    using (List; _∷_; [])
open import Data.Nat     as ℕ       using (ℕ; suc; zero)
open import Data.Product as Product using (_×_; _,_)

open import Agda.Builtin.Reflection
open import Reflection.TypeChecking.Monad.Syntax
open import Reflection.Argument

import Relation.Binary.Reasoning.Setoid as SetoidReasoning
import Algebra.Reasoning.Magma as MagmaReasoning

open import Algebra.Morphism.Group

infixl 7 _∙'_
data Expr {a} (A : Set a) : Set a where
  _∙'_ : Expr A → Expr A → Expr A
  ε'   : Expr A
  inv'  : Expr A → Expr A
  [_↑] : A → Expr A


module _ {c₁ ℓ₁ c₂ ℓ₂} {From : Group c₁ ℓ₁} {To : Group c₂ ℓ₂} (f : GroupMorphism From To) where

  open Group From renaming (_∙_ to _∙₁_;
                            ε to ε₁;
                            Carrier to Carrier₁;
                            _⁻¹ to _⁻¹₁;
                            _≈_ to _≈₁_;
                            inverseˡ to inverseˡ₁)
  open Group To renaming (_∙_ to _∙₂_;
                          ε to ε₂;
                          Carrier to Carrier₂;
                          _⁻¹ to _⁻¹₂;
                          _≈_ to _≈₂_;
                          setoid to setoid₂;
                          magma to magma₂;
                          ∙-cong to ∙-cong₂;
                          ∙-congʳ to ∙-congʳ₂;
                          ∙-congˡ to ∙-congˡ₂;
                          identityˡ to identityˡ₂;
                          identityʳ to identityʳ₂;
                          inverseʳ to inverseʳ₂;
                          assoc to assoc₂;
                          ⁻¹-cong to ⁻¹-cong₂)
  open GroupMorphism f

  open MagmaReasoning magma₂ hiding (Expr)

  [_↓] : Expr Carrier₁ → Carrier₁
  [ x ∙' y ↓] = [ x ↓] ∙₁ [ y ↓]
  [ ε'     ↓] = ε₁
  [ inv' x  ↓] = [ x ↓] ⁻¹₁
  [ [ x ↑] ↓] = x

  f[_↓] : Expr Carrier₁ → Carrier₂
  f[ e ↓] = morphism [ e ↓]

  f[_⇓] : Expr Carrier₁ → Carrier₂
  f[ x ∙' y ⇓] = f[ x ⇓] ∙₂ f[ y ⇓]
  f[ ε'     ⇓] = ε₂
  f[ inv' x  ⇓] = f[ x ⇓] ⁻¹₂
  f[ [ x ↑] ⇓] = morphism x

  proof : (e : Expr Carrier₁) → f[ e ↓] ≈₂ f[ e ⇓]
  proof (x ∙' y) = begin
    f[ x ∙' y ↓]                       ≡⟨⟩
    morphism ([ x ↓] ∙₁ [ y ↓])        ≈⟨ ∙-homo [ x ↓] [ y ↓] ⟩
    morphism [ x ↓] ∙₂ morphism [ y ↓] ≡⟨⟩
    f[ x ↓] ∙₂ f[ y ↓]                 ≈⟨ ∙-cong₂ (proof x) (proof y) ⟩
    f[ x ⇓] ∙₂ f[ y ⇓]                 ≡⟨⟩
    f[ x ∙' y ⇓]                       ∎
  proof ε' = ε-homo
  proof (inv' x) = begin
    f[ inv' x ↓]                                    ≈˘⟨ identityʳ₂ f[ inv' x ↓] ⟩
    f[ inv' x ↓] ◂ ⌊ ε₂ ⌋                           ≈˘⌊ inverseʳ₂ f[ x ↓] ⌋
    f[ inv' x ↓] ∙₂ (f[ x ↓] ∙₂ f[ x ↓] ⁻¹₂)        ≈˘⟨ assoc₂ f[ inv' x ↓] f[ x ↓] (f[ x ↓] T.⁻¹) ⟩
    ⌊ f[ inv' x ↓] ∙₂ f[ x ↓] ⌋ ▸ f[ x ↓] ⁻¹₂       ≈˘⌊ ∙-homo [ inv' x ↓] [ x ↓] ⌋
    ⌊ morphism ([ inv' x ↓] ∙₁ [ x ↓]) ⌋ ▸ f[ x ↓] ⁻¹₂ ≈⌊ ⟦⟧-cong $ inverseˡ₁ [ x ↓] ⌋
    ⌊ morphism ε₁ ⌋ ▸ f[ x ↓] ⁻¹₂                      ≈⌊ ε-homo ⌋
    ε₂ ∙₂ f[ x ↓] ⁻¹₂                               ≈⟨ identityˡ₂ (f[ x ↓] T.⁻¹) ⟩
    f[ x ↓] ⁻¹₂                                     ≈⟨ ⁻¹-cong₂ $ proof x ⟩
    f[ x ⇓] ⁻¹₂                                     ≡⟨⟩
    f[ inv' x ⇓]                                    ∎
  proof [ x ↑] = begin f[ [ x ↑] ↓] ∎

_==_ = primQNameEquality
{-# INLINE _==_ #-}

is-∙ : Name → Bool
is-∙ n = n == (quote Group._∙_)

is-ε : Name → Bool
is-ε n = n == (quote Group.ε)

is-⁻¹ : Name → Bool
is-⁻¹ n = n == (quote Group._⁻¹)

mutual

  ″∙″ : List (Arg Term) → Term
  ″∙″ (x ⟨∷⟩ y ⟨∷⟩ []) = quote _∙'_ ⟨ con ⟩ buildExpr x ⟨∷⟩ buildExpr y ⟨∷⟩ []
  ″∙″ (x ∷ xs) = ″∙″ xs
  ″∙″ _ = unknown

  ″⁻¹″ : List (Arg Term) → Term
  ″⁻¹″ (x ⟨∷⟩ []) = quote inv' ⟨ con ⟩ buildExpr x ⟨∷⟩ []
  ″⁻¹″ (x ∷ xs) = ″⁻¹″ xs
  ″⁻¹″ _ = unknown

  ″ε″ : Term
  ″ε″ = quote ε' ⟨ con ⟩ []

  [_↑]' : Term → Term
  [ t ↑]' = quote [_↑] ⟨ con ⟩ (t ⟨∷⟩ [])

  buildExpr : Term → Term
  buildExpr t@(def n xs) =
    if is-∙ n
      then ″∙″ xs
    else if is-⁻¹ n
      then ″⁻¹″ xs
    else if is-ε n
      then ″ε″
    else
      [ t ↑]'

  buildExpr t@(con n xs) =
    if is-∙ n
      then ″∙″ xs
    else if is-⁻¹ n
      then ″⁻¹″ xs
    else if is-ε n
      then ″ε″
    else
      [ t ↑]'

  buildExpr t = quote [_↑] ⟨ con ⟩ (t ⟨∷⟩ [])


getArgs : Term → Maybe (Term × Term)
getArgs (def _ xs) = go xs
  where
  go : List (Arg Term) → Maybe (Term × Term)
  go (vArg x ∷ vArg y ∷ []) = just (x , y)
  go (x ∷ xs)               = go xs
  go _                      = nothing
getArgs _ = nothing

constructSoln : Term → Term → Term → Term → Term
constructSoln f eq lhs rhs =
  let grp = quote GroupMorphism.to-group ⟨ def ⟩ f ⟨∷⟩ []
      f⇓ = quote f[_⇓]
      f↓ = quote f[_↓]
      l = buildExpr lhs
      r = buildExpr rhs in
  quote Group.trans ⟨ def ⟩ grp ⟨∷⟩
    (f⇓ ⟨ def ⟩ f ⟨∷⟩ l ⟨∷⟩ []) ⟅∷⟆
    (f↓ ⟨ def ⟩ f ⟨∷⟩ r ⟨∷⟩ []) ⟅∷⟆
    (f⇓ ⟨ def ⟩ f ⟨∷⟩ r ⟨∷⟩ []) ⟅∷⟆
    (quote Group.trans ⟨ def ⟩ grp ⟨∷⟩
      (f⇓ ⟨ def ⟩ f ⟨∷⟩ l ⟨∷⟩ []) ⟅∷⟆
      (f↓ ⟨ def ⟩ f ⟨∷⟩ l ⟨∷⟩ []) ⟅∷⟆
      (f↓ ⟨ def ⟩ f ⟨∷⟩ r ⟨∷⟩ []) ⟅∷⟆
      (quote Group.sym ⟨ def ⟩ grp ⟨∷⟩
        (f↓ ⟨ def ⟩ f ⟨∷⟩ l ⟨∷⟩ []) ⟅∷⟆
        (f⇓ ⟨ def ⟩ f ⟨∷⟩ l ⟨∷⟩ []) ⟅∷⟆
        (quote proof ⟨ def ⟩ f ⟨∷⟩ l ⟨∷⟩ []) ⟨∷⟩ [])
      ⟨∷⟩
      (quote GroupMorphism.⟦⟧-cong ⟨ def ⟩ f ⟨∷⟩ eq ⟨∷⟩ [])
      ⟨∷⟩ []
    )
    ⟨∷⟩
    (quote proof ⟨ def ⟩ f ⟨∷⟩ r ⟨∷⟩ [])
    ⟨∷⟩
    []

solve-macro : Term → Term → Term → TC _
solve-macro f eq hole = do
  eq' ← inferType eq >>= normalise
  just (lhs , rhs) ← returnTC (getArgs eq')
    where nothing → typeError (strErr "could not split arg" ∷ termErr eq ∷ [])
  let soln = constructSoln f eq lhs rhs
  debugPrint "" 1 (strErr "soln" ∷ termErr soln ∷ [])
  unify hole soln

macro
  ⟨_⟩⦅_⦆ : Term → Term → Term → TC _
  ⟨_⟩⦅_⦆ = solve-macro
