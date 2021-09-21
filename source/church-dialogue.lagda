Martin Escardo, 8 May 2013.

We modify

  http://www.cs.bham.ac.uk/~mhe/dialogue/dialogue.lagda
  http://www.cs.bham.ac.uk/~mhe/dialogue/dialogue.html
  http://www.cs.bham.ac.uk/~mhe/dialogue/dialogue.pdf

so that Church encodings of dialogue trees are used.

This version has no comments. Also, (1) we only account for
continuity, and (2) we provide the construction the modulus of
continuity but not its correctness, but the correctness should be
clear based on the proofs given in dialogue.*.

The practical result is that the computations are indeed much faster
using Church encodings.

A theoretical use of this is made in

  http://www.cs.bham.ac.uk/~mhe/dialogue/church-dialogue-internal.lagda
  http://www.cs.bham.ac.uk/~mhe/dialogue/church-dialogue-internal.html

to internalize moduli of continuity, as discussed in the paper
dialogue.pdf.

\begin{code}

module church-dialogue where

Ķ : ∀{X Y : Set} → X → Y → X
Ķ x y = x

Ş : ∀{X Y Z : Set} → (X → Y → Z) → (X → Y) → X → Z
Ş f g x = f x (g x)

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

rec : ∀{X : Set} → (X → X) → X → ℕ → X
rec f x  zero    = x
rec f x (succ n) = f(rec f x n)

data List (X : Set) : Set where
  []  : List X
  _∷_ : X → List X → List X

data _≡_ {X : Set} : X → X → Set where
  refl : ∀{x : X} → x ≡ x

data type : Set where
  ι   : type
  _⇒_ : type → type → type

data T : (σ : type) → Set where
  Zero : T ι
  Succ : T(ι ⇒ ι)
  Rec  : ∀{σ : type}     → T((σ ⇒ σ) ⇒ σ ⇒ ι ⇒ σ)
  K    : ∀{σ τ : type}   → T(σ ⇒ τ ⇒ σ)
  S    : ∀{ρ σ τ : type} → T((ρ ⇒ σ ⇒ τ) ⇒ (ρ ⇒ σ) ⇒ ρ ⇒ τ)
  _·_  : ∀{σ τ : type}   → T(σ ⇒ τ) → T σ → T τ

infixr 1 _⇒_
infixl 1 _·_

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

D : Set → Set → Set → Set → Set
D X Y Z A = (Z → A) → ((Y → A) → X → A) → A

η : {X Y Z A : Set} → Z → D X Y Z A
η z η' β' = η' z

β : {X Y Z A : Set} → (Y → D X Y Z A) → X → D X Y Z A
β Φ x η' β' = β' (λ y → Φ y η' β') x

D-rec : ∀{X Y Z A : Set} → (Z → A) → ((Y → A) → X → A) → D X Y Z A → A
D-rec η' β' d = d η' β'

dialogue : ∀{X Y Z : Set} → D X Y Z ((X → Y) → Z) → (X → Y) → Z
dialogue = D-rec (λ z α → z) (λ Φ x α → Φ(α x) α)

B : Set → Set → Set
B = D ℕ ℕ

kleisli-extension : ∀{X Y A : Set} → (X → B Y A) → B X A → B Y A
kleisli-extension f d η' β' = d (λ x → f x η' β') β'

B-functor : ∀{X Y A : Set} → (X → Y) → B X A → B Y A
B-functor f = kleisli-extension(λ x → η(f x))

B-Set⟦_⟧ : type → Set → Set
B-Set⟦ ι ⟧ A = B(Set⟦ ι ⟧) A
B-Set⟦ σ ⇒ τ ⟧ A = B-Set⟦ σ ⟧ A → B-Set⟦ τ ⟧ A

Kleisli-extension : ∀{X A : Set} {σ : type} → (X → B-Set⟦ σ ⟧ A) → B X A → B-Set⟦ σ ⟧ A
Kleisli-extension {X} {A} {ι} = kleisli-extension
Kleisli-extension {X} {A} {σ ⇒ τ} = λ g d s → Kleisli-extension {X} {A} {τ} (λ x → g x s) d

generic : {A : Set} → B ℕ A → B ℕ A
generic = kleisli-extension(β η)

zero' : {A : Set} → B ℕ A
zero' = η zero

succ' : {A : Set} → B ℕ A → B ℕ A
succ' = B-functor succ

rec' : ∀{σ : type}{A : Set} → (B-Set⟦ σ ⟧ A → B-Set⟦ σ ⟧ A) → B-Set⟦ σ ⟧ A → B ℕ A → B-Set⟦ σ ⟧ A
rec' {σ} {A} f x = Kleisli-extension {ℕ} {A} {σ} (rec f x)

B⟦_⟧ : ∀{σ : type}{A : Set} → T σ → B-Set⟦ σ ⟧ A
B⟦ Zero ⟧    = zero'
B⟦ Succ ⟧    = succ'
B⟦ Rec {σ} ⟧ = rec' {σ}
B⟦ K ⟧       = Ķ
B⟦ S ⟧       = Ş
B⟦ t · u ⟧   = B⟦ t ⟧ B⟦ u ⟧

dialogue-tree : {A : Set} → T((ι ⇒ ι) ⇒ ι) → B ℕ A
dialogue-tree t = B⟦ t ⟧ generic

max : ℕ → ℕ → ℕ
max zero y = y
max x zero = x
max (succ x) (succ y) = succ(max x y)

Mod-cont : B ℕ ((ℕ → ℕ) → List ℕ) → (ℕ → ℕ) → List ℕ
Mod-cont = D-rec (λ n α → []) (λ φ n α → n ∷ φ (α n) α)

Mod-cont' : B ℕ ((ℕ → ℕ) → ℕ)  → (ℕ → ℕ) → ℕ
Mod-cont' = D-rec (λ n α → zero) (λ φ n α → max (succ n) (φ (α n) α))

mod-cont : T((ι ⇒ ι) ⇒ ι) → (ℕ → ℕ) → List ℕ
mod-cont t = Mod-cont (dialogue-tree {(ℕ → ℕ) → List ℕ} t)

mod-cont' : T((ι ⇒ ι) ⇒ ι) → (ℕ → ℕ) → ℕ
mod-cont' t = Mod-cont' (dialogue-tree {(ℕ → ℕ) → ℕ} t)


-- Experiments follow:

infixl 0 _∷_

{-# BUILTIN NATURAL ℕ #-}

I : ∀{σ : type} → T(σ ⇒ σ)
I {σ} = S · K · (K {σ} {σ})
I-behaviour : ∀{σ : type}{x : Set⟦ σ ⟧} → ⟦ I ⟧ x ≡ x
I-behaviour = refl

number : ℕ → T ι
number zero = Zero
number (succ n) = Succ · (number n)

t₀ : T((ι ⇒ ι) ⇒ ι)
t₀ = K · (number 17)
t₀-interpretation : ⟦ t₀ ⟧ ≡ λ α → 17
t₀-interpretation = refl
example₀ : List ℕ
example₀ = mod-cont t₀ (λ i → i)

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

t₂ : T((ι ⇒ ι) ⇒ ι)
t₂ = Rec • t₁ • t₁
t₂-interpretation : ⟦ t₂ ⟧ ≡ λ α → rec α (α 17) (α 17)
t₂-interpretation = refl
example₂' : List ℕ
example₂' = mod-cont t₂ (λ i → i)

Add : T(ι ⇒ ι ⇒ ι)
Add = Rec · Succ
infixl 0 _+_
_+_ : ∀{γ} → T(γ ⇒ ι) → T(γ ⇒ ι) → T(γ ⇒ ι)
x + y = K · Add • x • y

t₃ : T((ι ⇒ ι) ⇒ ι)
t₃ = Rec • (v • Number 1) • (v • Number 2 + v • Number 3)
t₃-interpretation : ⟦ t₃ ⟧ ≡ λ α → rec α (α 1) (rec succ (α 2) (α 3))
t₃-interpretation = refl
example₃ : List ℕ
example₃ = mod-cont t₃ succ

length : {X : Set} → List X → ℕ
length [] = 0
length (x ∷ s) = succ(length s)

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
example₅'' : ℕ
example₅'' = mod-cont' t₅ succ
\end{code}
