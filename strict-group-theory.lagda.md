<link rel="stylesheet" href="/css/style-posts.css">
<link rel="stylesheet" href="/css/Agda.css">
<link href="https://fonts.googleapis.com/css?family=Source+Code+Pro:Regular,Semi-bold" rel="stylesheet" type="text/css">

# Strictly Associative Group Theory in Agda

<!--
```agda
open import Algebra.Bundles using (Group)
open import Level using (0ℓ)
module _ {𝓖 : Group 0ℓ 0ℓ} where

open Group 𝓖 renaming (refl to ≈-refl; setoid to G)

module _ where
  open import Relation.Binary.Reasoning.Setoid G
```
-->

## Introduction

Commonly, when one starts to learn group theory, they are given the axioms for a group and then shown a very basic proof which very carefully uses these axioms. As an example, one might show that the identity of a group is unique:

```agda
  identityˡ-unique : ∀ x y → x ∙ y ≈ y → x ≈ ε
  identityˡ-unique x y eq = begin
    x              ≈˘⟨ identityʳ x ⟩
    x ∙ ε          ≈˘⟨ ∙-congˡ (inverseʳ y) ⟩
    x ∙ (y ∙ y ⁻¹) ≈˘⟨ assoc x y (y ⁻¹) ⟩
    (x ∙ y) ∙ y ⁻¹ ≈⟨ ∙-congʳ eq ⟩
         y  ∙ y ⁻¹ ≈⟨ inverseʳ y ⟩
    ε              ∎
```

This works nicely for some small examples but as proofs get more complicated, a lot of the proof becomes moving brackets around and adding units, which can be considered boilerplate and obscures the interesting parts of the proof.

Instead of tackling these problems in group theory, it is usual to sweep all of these problems under the rug, not write any brackets anywhere, and assume that all the associativity problems could be solved if needed. Luckily for group theorists, it is rarely necessary to worry about these details. Unfortunately if instead we are interested in formalising some group theory, in a proof assistant such as [Agda](https://github.com/agda/agda), then this all becomes very necessary, as the computer does not trust us that all the associativity problems are unnecessary.

In this post, a method in which this "bracketless group theory" can be written in a proof assistant is presented, and some of the difficulties with this are described.

## The Idea

The key concept that will be used is that there are two different types of equality in Type Theory (which is the perspective taken for this post). The first type is propositional equality, which is written as `≈` above. `A ≈ B` effectively means that we can prove that `A` and `B` are equal. The second type of equality is definitional equality or judgmental equality. This is stronger than propositional equality and if two objects are definitionally equal it means that they are the same objects (or at least have the same normal form in the type theory).

What we had above was a propositional equality between `(x ∙ y) ∙ z` and `x ∙ (y ∙ z)`
```agda
  gassoc : ∀ x y z → (x ∙ y) ∙ z ≈ x ∙ (y ∙ z)
  gassoc x y z = assoc x y z
```

when what we really want is for this to be a definitional equality, which would allow us to treat these as the same object. We say that we have _strict associativity_ exactly when this equation holds by definition. Luckily there is such a structure that has this property, namely function composition. Suppose we have functions `f g h : X → X`. Then we have
<!--
```agda
module hidden where
  open import Relation.Binary.PropositionalEquality
  infixr 5 _∘_
  _∘_ : ∀ {X : Set} (f g : X → X) → X → X
  (f ∘ g) x = f (g x)
  infixr 4 _≃_
  _≃_ : ∀ {X Y : Set} (f g : X → Y) → Set
  _≃_ {X} f g = (x : X) → f x ≡ g x
```
-->
```agda
  sassoc : ∀ {X} (f g h : X → X) → (f ∘ g) ∘ h ≃ f ∘ (g ∘ h)
  sassoc f g h = λ x → refl
```
Therefore we can work with functions without ever having to worry about associativity problems. We can also note that we also eliminate the need for any identity laws with functions as for all sets `X`, we have an identity function `id : X → X` with
```agda
  id : ∀ {X : Set} → X → X
  id x = x
```

```agda
  sidentityˡ : ∀ {X} (f : X → X) → id ∘ f ≃ f
  sidentityˡ f = λ x → refl
```

```agda
  sidentityʳ : ∀ {X} (f : X → X) → f ∘ id ≃ f
  sidentityʳ f = λ x → refl
```

We say a structure has _strict units_ or is _strictly unital_ when this property holds.

### Cayley's Theorem
   Cayley's theorem gives us a translation from group operations to function composition. To understand what is says, we first need to introduce the notion of the symmetric group.

   <div class="definition">
   Given a set `X`, the symmetric group on `X`, written `Sym(X)`, is the group whose elements are permutations on `X`, operation is function composition, and inverses and identity are given by inverse and identity permutations.
   </div>

   The important thing of note here is that the group operation in the symmetric group is function composition, just as we wanted. We can now state Cayley's Theorem:

   <div class="theorem">
   Given a group `G`, there is an embedding (an injective homomorphism) from `G` into `Sym(G)`.
   </div>

   <div class="proof">
   Sketch: Define a homomorphism `⟦_⟧ : G → Sym(G)` by `⟦ g ⟧ = λ x → g ∙ x`. It is then routine to show that `⟦_⟧` is well defined (`⟦ g ⟧` is a permutation for each `g`), is a homomorphism, and is injective.
   </div>

   Suppose we want to prove `e₁ ≈ e₂`. The plan is to do the following steps.

   + Embed `e₁` and `e₂` into `Sym(G)` with `⟦_⟧`
   + Prove that `⟦ e₁ ⟧` and `⟦ e₂ ⟧` are equal as functions, with the benefit that function composition is strictly associative and unital.
   + Use injectivity to get that `e₁ ≈ e₂`

## Implementation
  All the ideas above have been implemented in [https://github.com/alexarice/Groups](https://github.com/alexarice/Groups). The corresponding version of the proof in the introduction is:
<!--
```agda
module _ where
  open import Algebra.Group.Symmetric 𝓖 renaming (e to id)
  open import Algebra.Group.Symmetric.Equality 𝓖
  open import Algebra.Group.Reasoning 𝓖
  open import Algebra.Group.Properties SymGroup using (invʳ; invˡ)
```
-->
```agda
  identity-is-unique-strong : ∀ a b → a ∙ b ≈ b → a ≈ ε
  identity-is-unique-strong a b p = begin⟨ ⟦⟧ ⟩
    ⟦ a ⟧                       ∘⟨⟩≣˘⟨ invʳ ⟦ b ⟧ ⟩
    ⟨ ⟦ a ⟧ ∘ ⟦ b ⟧ ⟩∘ inv ⟦ b ⟧   ≣⟨ ⟨ ⟦⟧ ⟩⦅ p ⦆ ⟩
    ⟨ ⟦ b ⟧ ∘ inv ⟦ b ⟧           ⟩≣⟨ invʳ ⟦ b ⟧ ⟩
    id                              ∎
```

  As a second example, here is the proof of left cancellation:

```agda
  left-cancellation : ∀ g h x → x ∙ g ≈ x ∙ h → g ≈ h
  left-cancellation g h x p = begin⟨ ⟦⟧ ⟩
    ⟨⟩∘ ⟦ g ⟧ ≣˘⟨ invˡ ⟦ x ⟧ ⟩
    inv ⟦ x ⟧ ∘⟨ ⟦ x ⟧ ∘ ⟦ g ⟧ ⟩≣⟨ ⟨ ⟦⟧ ⟩⦅ p ⦆ ⟩
    ⟨ inv ⟦ x ⟧ ∘ ⟦ x ⟧ ⟩∘ ⟦ h ⟧ ≣⟨ invˡ ⟦ x ⟧ ⟩
    ⟦ h ⟧ ∎
```

  and that the inverse operation is an anti homomorphism on the group operation:

```agda
  inv-of-composite : ∀ g h → (g ∙ h) ⁻¹ ≈ h ⁻¹ ∙ g ⁻¹
  inv-of-composite g h = begin⟨ ⟦⟧ ⟩
    inv (⟦ g ⟧ ∘ ⟦ h ⟧) ∘⟨⟩≣˘⟨ invʳ ⟦ g ⟧ ⟩
    inv (⟦ g ⟧ ∘ ⟦ h ⟧) ∘ ⟦ g ⟧ ∘⟨⟩∘ inv ⟦ g ⟧ ≣˘⟨ invʳ ⟦ h ⟧ ⟩
    ⟨ inv (⟦ g ⟧ ∘ ⟦ h ⟧) ∘ (⟦ g ⟧ ∘ ⟦ h ⟧) ⟩∘ inv ⟦ h ⟧ ∘ inv ⟦ g ⟧
      ≣⟨ invˡ (⟦ g ⟧ ∘ ⟦ h ⟧) ⟩
    inv ⟦ h ⟧ ∘ inv ⟦ g ⟧ ∎
```

  The rest of the post will be explaining the code above.

### Elimination of cong
   Perhaps the most obvious change from the original code is the addition of the angle brackets `⟨` and `⟩`. These allow us to apply an equality to a part of the expression we are working on. Instead of having to manually use a `cong` function to manipulate the equality (as well as making it unreadable), we instead use the syntax above which allows the appropriate equalities to be automatically put in.

   This is made possible due to the simplicity of the expressions. As each expression is now effectively a finite list of functions, it becomes very easy to split it into a focus, which we manipulate, as well as expressions that occur before and after the focus.

### Strict associativity and unitality
   The above proof shows that the need for associativity operations has been removed. The result of the first equality in the proof is:

```agda-no-compile
⟦ a ⟧ ∘ (⟦ b ⟧ ∘ inv ⟦ b ⟧)
```

and yet in the next line we treat it as:

```agda-no-compile
(⟦ a ⟧ ∘ ⟦ b ⟧) ∘ inv ⟦ b ⟧
```

without telling Agda how to deal with this. This is possible as the terms have the same normal form (this is not actually true, see [Equality between functions](#equality-between-functions)).

We can also see that unitality has been taken care of. In the first line it has been implicitly assumed that an identity can be inserted on the right of the expression.

## Equality between functions
   The choice of equality between functions is crucial to making this syntax work. The complication is that we have said function composition is strictly associative but glossed over that we are working with permutations or invertible functions.

   Above, the `∘` operator is not just composition of functions, but is composition of invertible functions, which joins the proofs that each component is invertible to get a proof that the whole composite is invertible. It turns out this is _not_ a strictly associative operation. However if we make sure we only compare the function components of the invertible functions, then strict associativity returns.

   This would lead us to the following definition of equality between invertible functions.

<!--
```agda
module hidden2 where
  open import Algebra.Group.Symmetric 𝓖 renaming (e to id)
  open import Function.Equality using (_⇨_;Π;_⟶_) renaming (_∘_ to _*_)
  open import Function.Inverse using (Inverse)
  open import Level
  open import Relation.Binary using (Setoid; _⇒_)

  open Π
  open Inverse

  funcSetoid : Setoid _ _
  funcSetoid = G ⇨ G
  open module F = Setoid funcSetoid using () renaming (_≈_ to _≃_)
```
-->

```
  _∼_ : Sym → Sym → Set
  f ∼ g = to f ≃ to g
```

Where Sym is the type of permutations on the group and `≃` is pointwise equality of functions.

 This has the advantage that it does not remember any of the invertibility data and so we can have all the nice features mentioned above. However, it turns out that this forgets too much invertibility data, in that if the implementation is made with this equality, then Agda will complain everywhere about implicit arguments that it cannot resolve. The next thing we might try is to remember the invertibility data but do not check whether it is equal. This leads to the following definition.

```agda
  record SymEq (f g : Sym) : Set where
    field
      eq : to f ≃ to g

  _≣_ : Sym → Sym → Set
  _≣_ = SymEq
```

This ends up being a nice form of equality which we use to define the symmetric group. Unfortunately, it runs into problems with invertibility data not lining up if we try to use it in the syntax above. It turns out we need another type of equality, where we only remember the invertibility data for the second argument. This clears all the implicit argument problems without introducing any associativity problems.

```
  record PartSymEq (f : G ⟶ G) (g : Sym) : Set where
    field
      peq : f ≃ to g

  _≣'_ : Sym → Sym → Set
  f ≣' g = PartSymEq (to f) g
```

### Dealing with homomorphisms
   So far we have not covered the last step of the proof strategy, which was using injectivity transform function equality to group element equality. This is a very simple procedure, however it does not usually do what we want. Consider the proof that identities are unique. Injectivity gives us something of the form:

```agda-no-compile
  ⟦ a ⟧ ≣ ⟦ ε ⟧ → a ≈ ε
```

but what we actually wanted was:

```agda-no-compile
  ⟦ a ⟧ ≣ id → a ≈ ε
```

We also have the same problem going the opposite direction. In the proof we have an argument of the form:

```agda-no-compile
  a ∙ b ≈ b
```

If were naively transport this using the inclusion we would get:

```agda-no-compile
  ⟦ a ∙ b ⟧ ≣ ⟦ b ⟧
```

when what we really wanted was:

```agda-no-compile
  ⟦ a ⟧ ∘ ⟦ b ⟧ ≣ ⟦ b ⟧
```

The proofs that these imply each other are not too difficult but applying them to each case is tedious and makes the proofs more convoluted which defeats the original purpose of this construction. Therefore two reflection helpers have been made to automate this process. The first is `⟨_⟩⦅_⦆`, which solves the second problem. This takes a homomorphism and an equality and applies as many homomorphism rules as possible to the equality. It does this by inspecting the terms of the left and right hand side using reflection and using this to work out which rules to apply.

<!--
```agda
module _ where
  open import Algebra.Group.Symmetric 𝓖 renaming (e to id)
  open import Algebra.Group.Symmetric.Equality 𝓖
  open import Algebra.Group.Reasoning 𝓖
```
-->

```agda
  test : ∀ a b → a ≈ b → ⟦ a ⟧ ≣ ⟦ b ⟧
  test a b p = ⟨ ⟦⟧ ⟩⦅ p ⦆

  test2 : ∀ a b → a ∙ b ≈ b → ⟦ a ⟧ ∘ ⟦ b ⟧ ≣ ⟦ b ⟧
  test2 a b p = ⟨ ⟦⟧ ⟩⦅ p ⦆

  test3 : ∀ x y z
        → x ∙ (y ⁻¹ ∙ ε) ≈ z ∙ z
        → ⟦ x ⟧ ∘ (inv ⟦ y ⟧ ∘ id) ≣ ⟦ z ⟧ ∘ ⟦ z ⟧
  test3 x y z p = ⟨ ⟦⟧ ⟩⦅ p ⦆
```

The second reflection helper is wrapped in the `begin⟨_⟩_` function. This takes care of the first problem we had, again by using reflection to find the term needed and applying the appropriate rules to get the given proof in the form needed.

## Limitations
There are currently a few limitations with this system:
- The syntax is not ideal. One problem is that it currently seems necessary to pass the homomorphism into the reflection helper each time it is used though this is probably fixable. Something which is less fixable is the angle bracket syntax for dealing with congs being "stuck to" the equality symbol. This is caused by Agda syntax requiring that you alternate holes and non holes, where we would like to be able to put two non holes next to each other.
- The reflection helpers are very slow. In the current version of Agda (2.6.1), compiling these files is very slow which makes them painful to work with.
- Agda is not great at telling you what should go in a hole with this syntax. Where the reflection helpers are used, it will tell you it wants something of a type labelled by some mysterious number. Even when this isn't the case, the use of records for the permutations sometimes causes a mess when one tries to solve a hole.

## Thanks
Thanks goes to Martín Escardó, who suggested the possibility of using Cayley's Theorem and convinced me to write this post. I would also like to thank all members of the Birmingham theory group who I have discussed this work with.
