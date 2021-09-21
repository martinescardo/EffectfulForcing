-- Martin Escardo & Paulo Oliva, Fri 24-25 Feb 2017
-- 
-- Conversion of dialogue trees to Brouwer trees.

{-# OPTIONS --without-K #-}

data ℕ : Set where 
 zero : ℕ              
 succ : ℕ → ℕ       

data _≡_ {X : Set} : X → X → Set where
 refl : {x : X} → x ≡ x

trans : {X : Set} {x y z : X} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

infix  1 _≡_
infixr 0 _≡⟨_⟩_

_≡⟨_⟩_ : {X : Set} (x : X) {y z : X} → x ≡ y → y ≡ z → x ≡ z
_ ≡⟨ p ⟩ q = trans p q

_∎ : {X : Set } (x : X) → x ≡ x
_∎ _ = refl

-- Dialogue trees:

data D : Set where 
 η : ℕ → D
 β : (ℕ → D) → ℕ → D

-- We use φ to range over forests of dialogue trees, that is,
-- functions ℕ → D.

-- Dialogue trees represent functions (ℕ → ℕ) → ℕ:

deval : D → (ℕ → ℕ) → ℕ
deval (η k)   α = k
deval (β φ n) α = deval (φ(α n)) α

-- Brouwer trees:

data B : Set where
 η : ℕ → B
 δ : (ℕ → B) → B

-- We use γ to range over forests of Brower trees.

-- Brouwer trees represent functions (ℕ → ℕ) → ℕ too:

beval : B → (ℕ → ℕ) → ℕ
beval (η k) α = k
beval (δ γ) α = beval (γ(α zero)) (λ i → α(succ i))

-- Conversion from dialogue to Brouwer trees, with two auxiliary
-- functions follow and β':

follow : ℕ → B → B
follow n (η k) = η k
follow n (δ γ) = γ n

-- The function β' simulates D's constructor β in B:

β' : (ℕ → B) → ℕ → B
β' γ zero     = δ (λ i → follow i (γ i))
β' γ (succ n) = δ (λ i → β' (λ j → follow i (γ j)) n) 

-- Conversion is the unique homomorphism w.r.t. D-structure:

convert : D → B
convert (η k)   = η k
convert (β φ n) = β' (λ i → convert (φ i)) n

-- The correctness proof of the function convert uses two lemmas, one
-- for the function follow and the other for the function β':

-- By cases on b:

follow-lemma : (b : B) (α : ℕ → ℕ)
             → beval b α ≡ beval (follow (α zero) b) (λ i → α (succ i)) 
follow-lemma (η k) α = refl
follow-lemma (δ φ) α = refl

-- By induction on n, using follow-lemma both in the base case and the
-- induction step:

β'-lemma : (n : ℕ) (φ : ℕ → B) (α : ℕ → ℕ)
         → beval (φ(α n)) α ≡ beval (β' φ n) α

β'-lemma zero φ α =
  beval (φ(α zero)) α                                    ≡⟨ follow-lemma ((φ(α zero))) α ⟩
  beval (follow (α zero) (φ(α zero))) (λ i → α (succ i)) ≡⟨ refl ⟩
  beval (δ (λ i → follow i (φ i))) α                     ≡⟨ refl ⟩
  beval (β' φ zero) α ∎

β'-lemma (succ n) φ α = 
  beval (φ(α(succ n))) α                                       ≡⟨ follow-lemma (φ(α(succ n))) α ⟩
  beval (follow (α zero) (φ(α(succ n)))) (λ i → α(succ i))     ≡⟨ β'-lemma n (λ j → follow (α zero) (φ j)) (λ i → α (succ i)) ⟩
  beval (β' (λ j → follow (α zero) (φ j)) n) (λ i → α(succ i)) ≡⟨ refl ⟩
  beval (δ (λ i → β' (λ j → follow i (φ j)) n)) α              ≡⟨ refl ⟩
  beval (β' φ(succ n)) α ∎

-- By induction on d, using β'-lemma in the induction step:

convert-correctness : (d : D) (α : ℕ → ℕ) → deval d α ≡ beval (convert d) α
convert-correctness (η k)   α = refl
convert-correctness (β φ n) α = 
  deval (φ(α n)) α                       ≡⟨ convert-correctness (φ(α n)) α ⟩
  beval (convert (φ(α n))) α             ≡⟨ β'-lemma n (λ i → convert (φ i)) α ⟩
  beval (β' (λ i → convert (φ i)) n) α ∎
  
