Martin Escardo, 8 May 2013.

This is based on

  http://www.cs.bham.ac.uk/~mhe/dialogue/dialogue.lagda
  http://www.cs.bham.ac.uk/~mhe/dialogue/dialogue.html
  http://www.cs.bham.ac.uk/~mhe/dialogue/dialogue.pdf

and in turn on

  http://www.cs.bham.ac.uk/~mhe/dialogue/church-dialogue.lagda
  http://www.cs.bham.ac.uk/~mhe/dialogue/church-dialogue.html

which uses Church encoding of dialogue trees, and should be consulted
before trying to understand what follows.

We modify the latter so as to internalize the modulus of
continuity. That is, we now have a function

   internal-mod-cont : T((ι ⇒ ι) ⇒ ι) → T((ι ⇒ ι) ⇒ ι)

that given a term t : T((ι⇒ι)⇒ι) produces term m : T((ι⇒ι)⇒ι) such
that m defines the modulus of continuity of t. We use Church encoding
to represent dialogue trees within system T. This also shows that
dialogue trees of terms of type (ι ⇒ ι) ⇒ ι cannot be very tall,
because system T can only define trees of height smaller than ε₀.

This version has very few comments. Also, (1) we only account for
continuity, and (2) we provide the construction of the modulus of
continuity, but we don't fully prove its correctness, which should
nevertheless be clear based on the proofs given in dialogue.*.

For the purposes of this, it would have been better to have worked
with the lambda-calculus version of system T, as the reader can see.
This short file takes a minute to type-check, due to the occurrence of
large combinatory terms with hundreds of implicit parameters.

\begin{code}

module church-dialogue-internal where

data _≡_ {X : Set} : X → X → Set where
  refl : ∀{x : X} → x ≡ x

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

rec : ∀{X : Set} → (X → X) → X → ℕ → X
rec f x  zero    = x
rec f x (succ n) = f(rec f x n)

-- System T type expressions:
data type : Set where
  ι   : type
  _⇒_ : type → type → type

-- (Combinatory) system T terms:
data T : (σ : type) → Set where
  Zero : T ι
  Succ : T(ι ⇒ ι)
  Rec  : ∀{σ : type}     → T((σ ⇒ σ) ⇒ σ ⇒ ι ⇒ σ)
  K    : ∀{σ τ : type}   → T(σ ⇒ τ ⇒ σ)
  S    : ∀{ρ σ τ : type} → T((ρ ⇒ σ ⇒ τ) ⇒ (ρ ⇒ σ) ⇒ ρ ⇒ τ)
  _·_  : ∀{σ τ : type}   → T(σ ⇒ τ) → T σ → T τ

infixr 1 _⇒_
infixl 1 _·_

-- The standard semantics of T is not needed for this construction,
-- but it is useful to make sure the T translation is really what we
-- intend:

Ķ : ∀{X Y : Set} → X → Y → X
Ķ x y = x

Ş : ∀{X Y Z : Set} → (X → Y → Z) → (X → Y) → X → Z
Ş f g x = f x (g x)

Set⟦_⟧ : type → Set
Set⟦ ι ⟧ = ℕ
Set⟦ σ ⇒ τ ⟧ = Set⟦ σ ⟧ → Set⟦ τ ⟧

⟦_⟧ : ∀{σ : type} → T σ → Set⟦ σ ⟧
⟦ Zero ⟧  = zero
⟦ Succ ⟧  = succ
⟦ Rec ⟧   = rec
⟦ K ⟧     = Ķ
⟦ S ⟧     = Ş
⟦ t · u ⟧ = ⟦ t ⟧ ⟦ u ⟧

-- Church encoding of dialogue trees, internal to system T:
D : type → type → type → type → type
D X Y Z A = (Z ⇒ A) ⇒ ((Y ⇒ A) ⇒ X ⇒ A) ⇒ A

I : ∀{σ : type} → T(σ ⇒ σ)
I {σ} = S · K · (K {σ} {σ})

-- The following is automatically translated from λ z η' β' → η' z using the
-- calculator http://www.cantab.net/users/antoni.diller/brackets/intro.html:
η : {X Y Z A : type} → T(Z ⇒ D X Y Z A)
η = S · (S · (K · S) · (S · (S · (K · S) · (S · (K · K) · (K · S))) · (S · (S · (K · S) · (S · (K · K) · (K · K))) · (K · I)))) · (S · (S · (K · S) · (S · (K · K) · (K · K))) · (S · (K · K) · I))

-- This translation is correct:
η-behaviour : {X Y Z A : type} → ∀ z η' β' → ⟦ η {X} {Y} {Z} {A} ⟧ z η' β' ≡ η' z
η-behaviour z η' β' = refl

-- Then we translate λ φ x η' β' → β' (λ y → φ y η' β') x:
β : {X Y Z A : type} → T (((Y ⇒ D X Y Z A) ⇒ X ⇒ D X Y Z A))
β = S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · S))))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · S))))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · I)))))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · S))))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · S))))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · K))))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · S))))))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · S))))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · S))))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · K))))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · S))))))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · S))))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · S))))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · K))))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · S))))))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · S))))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · K))))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · K))))))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · K))))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) · I)))))))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · K))))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · I))))))))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · S))))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · K))))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · K))))))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · K))))) ·(S ·(K · K) ·(K · I))))))))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · S))))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · K))))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · K))))))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · I))))))))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · K))))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(K · I)))

β-behaviour : {X Y Z A : type} → ∀ φ x η' β' → ⟦ β {X} {Y} {Z} {A} ⟧ φ x η' β' ≡ β' (λ y → φ y η' β') x
β-behaviour φ x η' β' = refl

B : type → type → type
B = D ι ι

-- The following is translated from λ f d η' β' → d (λ x → f x η' β') β':
kleisli-extension : ∀{X Y A : type} → T((X ⇒ B Y A) ⇒ B X A ⇒ B Y A)
kleisli-extension = S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · S))))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · S))))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · K))))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(K · I)))))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · S))))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · S))))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · K))))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · S))))))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · S))))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · S))))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · K))))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · S))))))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · S))))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · S))))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · K))))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · S))))))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · S))))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · K))))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · K))))))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · K))))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) · I)))))))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · K))))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · I))))))))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · S))))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · K))))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · K))))))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · K))))) ·(S ·(K · K) ·(K · I))))))))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · S))))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · K))))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · K))))))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · I))))))))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · I)))

kleisli-extension-behaviour : ∀{X Y A : type} → ∀ f d η' β' → ⟦ kleisli-extension {X} {Y} {A} ⟧ f d η' β' ≡ d (λ x → f x η' β') β'
kleisli-extension-behaviour f d η' β' = refl

-- The following is translated from λ f → kleisli-extension(λ x → η(f x)):
B-functor : ∀{X Y A : type} → T((X ⇒ Y) ⇒ B X A ⇒ B Y A)
B-functor = S ·(K · kleisli-extension) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · η))) ·(S ·(S ·(K · S) ·(S ·(K · K) · I)) ·(K · I)))

B-functor-behaviour : ∀{X Y A : type} → ∀ f → ⟦ B-functor {X} {Y} {A} ⟧ f ≡ ⟦ kleisli-extension ⟧ (λ x → ⟦ η ⟧ (f x))
B-functor-behaviour f = refl

-- Translation of types:
B-type⟦_⟧ : type → type → type
B-type⟦ ι ⟧ A = B ι A
B-type⟦ σ ⇒ τ ⟧ A = B-type⟦ σ ⟧ A ⇒ B-type⟦ τ ⟧ A

-- The second equation of the following is translated from λ g d s → Kleisli-extension {X} {A} {τ} (λ x → g x s) d:
Kleisli-extension : ∀{X A : type} {σ : type} → T((X ⇒ B-type⟦ σ ⟧ A) ⇒ B X A ⇒ B-type⟦ σ ⟧ A)
Kleisli-extension {X} {A} {ι} = kleisli-extension
Kleisli-extension {X} {A} {σ ⇒ τ} = S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · (Kleisli-extension {X} {A} {τ})))))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · S))))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · S))))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · K))))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) · I)))))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · I))))))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · K))))) ·(S ·(K · K) ·(K · I))))))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(K · I))

Kleisli-extension-behaviour : ∀{X A : type} {σ τ : type} → ∀ g d s
                            → ⟦ Kleisli-extension {X} {A} {σ ⇒ τ} ⟧ g d s ≡ ⟦ Kleisli-extension {X} {A} {τ} ⟧ (λ x → g x s) d
Kleisli-extension-behaviour g d s = refl


zero' : {A : type} → T(B ι A)
zero' = η · Zero

succ' : {A : type} → T(B ι A ⇒ B ι A)
succ' =  B-functor · Succ

--  Translation of λ f x →  Kleisli-extension {ι} {A} {σ} (rec f x):
rec' : ∀{σ A : type} → T((B-type⟦ σ ⟧ A ⇒ B-type⟦ σ ⟧ A) ⇒ B-type⟦ σ ⟧ A ⇒ B ι A ⇒ B-type⟦ σ ⟧ A)
rec' {σ} {A} = S · (S · (K · S) · (S · (K · K) · (K · (Kleisli-extension {ι} {A} {σ})))) · (S · (S · (K · S) · (S · (S · (K · S) · (S · (K · K) · (K · Rec))) · (S · (K · K) · I))) · (K · I))

rec'-behaviour : ∀{σ A : type} → ∀ f x →  ⟦ rec' {σ} {A} ⟧ f x ≡ ⟦ Kleisli-extension {ι} {A} {σ} ⟧ (rec f x)
rec'-behaviour f x = refl

-- (Compositional) translation of terms:
B⟦_⟧ : ∀{σ : type}{A : type} → T σ → T(B-type⟦ σ ⟧ A)
B⟦ Zero ⟧    = zero'
B⟦ Succ ⟧    = succ'
B⟦ Rec {σ} ⟧ = rec' {σ}
B⟦ K ⟧       = K
B⟦ S ⟧       = S
B⟦ t · u ⟧   = B⟦ t ⟧ · B⟦ u ⟧

-- Given a term of type (ι ⇒ ι) ⇒ ι, we calculate a term defining its dialogue tree:
generic : {A : type} → T(B ι A ⇒ B ι A)
generic = kleisli-extension · (β · η)

dialogue-tree : {A : type} → T((ι ⇒ ι) ⇒ ι) → T(B ι A)
dialogue-tree t = B⟦ t ⟧ · generic

-- With this it is now easy to internalize the modulus of continuity:

Add : T(ι ⇒ ι ⇒ ι)
Add = Rec · Succ

-- I will cheat for the moment, and add rather than take max, because
-- it is difficult to compute max with the iterator Rec. This is
-- benign cheating, which gives a worse, but correct modulus.

Max : T(ι ⇒ ι ⇒ ι)
Max = Add

-- The modulus of continuity can be calculated from a dialogue tree.
-- Translation of λ d → d (λ n α → zero) (λ φ n α → max (succ n) (φ (α n) α))
Mod-cont : T(B ι ((ι ⇒ ι) ⇒ ι) ⇒ (ι ⇒ ι) ⇒ ι)
Mod-cont = S ·(S · I ·(S ·(K · K) ·(S ·(K · K) ·(K · Zero)))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · S))))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · S))))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · K))))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · Max))))))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · S))))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · K))))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · Succ))))))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · K))))) ·(S ·(K · K) ·(K · I)))))))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · S))))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · S))))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · K))))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(K · I)))))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · S))))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · I)))))) ·(S ·(S ·(K · S) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · S))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · K))))) ·(S ·(K · K) ·(K · I)))))))) ·(S ·(S ·(K · S) ·(S ·(K · K) ·(K · K))) ·(S ·(K · K) ·(K · I)))))

-- Instead of describing the above behaviour, we describe the
-- corresponding pattern-matching behaviour, for clarity:
Mod-cont-behaviour₀ : ∀ n α → ⟦ Mod-cont ⟧ (⟦ η ⟧ n) α ≡ zero
Mod-cont-behaviour₀ n α = refl

Mod-cont-behaviour₁ : ∀ φ n α → ⟦ Mod-cont ⟧ (⟦ β ⟧ φ n) α ≡ ⟦ Max ⟧ (succ n) (⟦ Mod-cont ⟧ (φ(α n)) α)
Mod-cont-behaviour₁ φ n α = refl

-- To calculate the modulus term of a term, we first calculate the dialogue-tree term and then walk the tree:
internal-mod-cont : T((ι ⇒ ι) ⇒ ι) → T((ι ⇒ ι) ⇒ ι)
internal-mod-cont t = Mod-cont · (dialogue-tree {(ι ⇒ ι) ⇒ ι} t)

\end{code}

That's it.

Experiments follow:

\begin{code}

external-mod-cont : T((ι ⇒ ι) ⇒ ι) → (ℕ → ℕ) → ℕ
external-mod-cont t = ⟦ internal-mod-cont t ⟧

{-# BUILTIN NATURAL ℕ #-}

number : ℕ → T ι
number zero = Zero
number (succ n) = Succ · (number n)

t₀ : T((ι ⇒ ι) ⇒ ι)
t₀ = K · (number 17)
t₀-interpretation : ⟦ t₀ ⟧ ≡ λ α → 17
t₀-interpretation = refl
example₀ : ℕ
example₀ = external-mod-cont t₀ (λ i → i)

v : ∀{γ : type} → T(γ ⇒ γ)
v = I

infixl 1 _•_
_•_ : ∀{γ σ τ : type} → T(γ ⇒ σ ⇒ τ) → T(γ ⇒ σ) → T(γ ⇒ τ)
f • x = S · f · x

Number : ∀{γ} → ℕ → T(γ ⇒ ι)
Number n = K · (number n)

t₁ : T((ι ⇒ ι) ⇒ ι)
t₁ = v • (Number 17)
t₁-interpretation : ⟦ t₁ ⟧ ≡ λ α → α 17
t₁-interpretation = refl
example₁ : ℕ
example₁ = external-mod-cont t₁ (λ i → i)

t₂ : T((ι ⇒ ι) ⇒ ι)
t₂ = Rec • t₁ • t₁
t₂-interpretation : ⟦ t₂ ⟧ ≡ λ α → rec α (α 17) (α 17)
t₂-interpretation = refl
example₂ : ℕ
example₂ = external-mod-cont t₂ (λ i → i)

infixl 0 _+_
_+_ : ∀{γ} → T(γ ⇒ ι) → T(γ ⇒ ι) → T(γ ⇒ ι)
x + y = K · Add • x • y

t₃ : T((ι ⇒ ι) ⇒ ι)
t₃ = Rec • (v • Number 1) • (v • Number 2 + v • Number 3)
t₃-interpretation : ⟦ t₃ ⟧ ≡ λ α → rec α (α 1) (rec succ (α 2) (α 3))
t₃-interpretation = refl
example₃ : ℕ
example₃ = external-mod-cont t₃ succ

t₄ : T((ι ⇒ ι) ⇒ ι)
t₄ = Rec • ((v • (v • Number 2)) + (v • Number 3)) • t₃
t₄-interpretation : ⟦ t₄ ⟧ ≡ λ α → rec α (rec succ (α (α 2)) (α 3)) (rec α (α 1) (rec succ (α 2) (α 3)))
t₄-interpretation = refl

t₅ : T((ι ⇒ ι) ⇒ ι)
t₅ = Rec • (v • (v • t₂ + t₄)) • (v • Number 2)
t₅-explicitly : t₅ ≡   (S · (S · Rec · (S · I · (S · (S · (K · (Rec · Succ)) · (S · I · (S
                    · (S · Rec · (S · I · (K · (number 17)))) · (S · I · (K · (number 17))))))
                    · (S · (S · Rec · (S · (S · (K · (Rec · Succ)) · (S · I · (S · I · (K · (number 2)))))
                    · (S · I · (K · (number 3))))) · (S · (S · Rec · (S · I · (K · (number 1))))
                    · (S · (S · (K · (Rec · Succ)) · (S · I · (K · (number 2)))) · (S · I · (K
                    · (number 3))))))))) · (S · I · (K · (number 2))))
t₅-explicitly = refl
t₅-interpretation : ⟦ t₅ ⟧ ≡ λ α → rec α (α(rec succ (α(rec α (α 17) (α 17)))
                                              (rec α (rec succ (α (α 2)) (α 3))
                                              (rec α (α 1) (rec succ (α 2) (α 3)))))) (α 2)
t₅-interpretation = refl
example₅ : ℕ
example₅ = external-mod-cont t₅ succ

\end{code}
