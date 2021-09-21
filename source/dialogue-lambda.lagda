Martin Escardo 22-23 May 2013, updated 24 May after a fruitful
discussion in the Agda mailing list, and 26 May.


This is an Agda proof that the system T definable functions

  (ℕ → ℕ) → ℕ

are continuous, and that their restrictions from the Baire space
(ℕ → ℕ) of sequences of natural numbers to the Cantor space (ℕ → ℕ₂)
of binary sequences are uniformly continuous.

We provided such a proof for the combinatory version of system T in

 http://www.cs.bham.ac.uk/~mhe/dialogue/dialogue.lagda          (Agda/latex file)
 http://www.cs.bham.ac.uk/~mhe/dialogue/dialogue.html           (html rendering)
 http://www.cs.bham.ac.uk/~mhe/dialogue/dialogue.pdf            (conference article)
 http://www.cs.bham.ac.uk/~mhe/dialogue/laconic-dialogue.lagda  (Agda without comments)
 http://www.cs.bham.ac.uk/~mhe/dialogue/laconic-dialogue.html   (html rendering)

Here we work with the lambda-calculus version of system T instead. We
work with de Bruijn indices. The proof for this version of system T is
no more difficult, conceptually, but is more demanding on the routine
details.

Additionally, we now let Rec be the primitive recursion combinator
rather than the iteration combinator.

The initial part on dialogues and (uniform) continuity is literally
the same as in the above development. The brief preliminaries are
slightly extended.

\begin{code}

module dialogue-lambda where

\end{code}

Preliminaries:

\begin{code}

_∘_ : ∀{X Y Z : Set} → (Y → Z) → (X → Y) → (X → Z)
g ∘ f = λ x → g(f x)

data ℕ₂ : Set where
  ₀ : ℕ₂
  ₁ : ℕ₂

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

rec : ∀{X : Set} → (ℕ → X → X) → X → ℕ → X
rec f x  zero    = x
rec f x (succ n) = f n (rec f x n)

data List (X : Set) : Set where
  []  : List X
  _∷_ : X → List X → List X

data Tree (X : Set) : Set where
  empty  : Tree X
  branch : X → (ℕ₂ → Tree X) → Tree X

data Σ {X : Set} (Y : X → Set) : Set where
  _,_ : ∀(x : X)(y : Y x) → Σ {X} Y

π₀ : ∀{X : Set} {Y : X → Set} → (Σ \(x : X) → Y x) → X
π₀(x , y) = x

π₁ : ∀{X : Set} {Y : X → Set} (t : Σ \(x : X) → Y x) → Y(π₀ t)
π₁(x , y) = y

data _≡_ {X : Set} : X → X → Set where
  refl : ∀{x : X} → x ≡ x

sym : ∀{X : Set} {x y : X} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀{X : Set} {x y z : X} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

cong : ∀{X Y : Set} (f : X → Y) → ∀{x₀ x₁ : X} → x₀ ≡ x₁ → f x₀ ≡ f x₁
cong f refl = refl

cong₂ : ∀{X Y Z : Set} (f : X → Y → Z) {x₀ x₁ : X} {y₀ y₁ : Y} → x₀ ≡ x₁ → y₀ ≡ y₁ → f x₀ y₀ ≡ f x₁ y₁
cong₂ f refl refl = refl

subst : {X : Set}{Y : X → Set}{x x' : X} → x ≡ x' → Y x → Y x'
subst refl y = y

\end{code}

We work with vector types which notationally grow at the end rather
than the head.  This is because we use vector types to represent
contexts, which traditionally grow at the end:

\begin{code}

data _^_ (X : Set) : ℕ → Set where
  〈〉  : X ^ zero
  _’_ : {n : ℕ} → X ^ n → X → X ^ (succ n)

infixl 6  _’_

data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin(succ n)
  succ : {n : ℕ} → Fin n → Fin(succ n)

_[_] : {X : Set} {n : ℕ} → X ^ n → Fin n → X
(xs ’ x) [ zero ] = x
(xs ’ x) [ succ i ] = xs [ i ]

\end{code}

Dialogue trees (no difference with the original treatment):

\begin{code}

data D (X Y Z : Set) : Set where
  η : Z → D X Y Z
  β : (Y → D X Y Z) → X → D X Y Z

dialogue : ∀{X Y Z : Set} → D X Y Z → (X → Y) → Z
dialogue (η z)   α = z
dialogue (β φ x) α = dialogue (φ(α x)) α

eloquent : ∀{X Y Z : Set} → ((X → Y) → Z) → Set
eloquent f = Σ \d → ∀ α → dialogue d α ≡ f α

\end{code}

Continuity (no difference either):

\begin{code}

Baire : Set
Baire = ℕ → ℕ

B : Set → Set
B = D ℕ ℕ

data _≡[_]_ {X : Set} : (ℕ → X) → List ℕ → (ℕ → X) → Set where
  []  : ∀{α α' : ℕ → X} → α ≡[ [] ] α'
  _∷_ : ∀{α α' : ℕ → X}{i : ℕ}{s : List ℕ} → α i ≡ α' i → α ≡[ s ] α' → α ≡[ i ∷ s ] α'

continuous : (Baire → ℕ) → Set
continuous f = ∀(α : Baire) → Σ \(s : List ℕ) → ∀(α' : Baire) → α ≡[ s ] α' → f α ≡ f α'

dialogue-continuity : ∀(d : B ℕ) → continuous(dialogue d)
dialogue-continuity (η n) α = ([] , lemma)
  where
   lemma : ∀ α' → α ≡[ [] ] α' → n ≡ n
   lemma α' r = refl
dialogue-continuity (β φ i) α = ((i ∷ s) , lemma)
  where
   IH : ∀(i : ℕ) → continuous(dialogue(φ(α i)))
   IH i = dialogue-continuity (φ(α i))
   s : List ℕ
   s = π₀(IH i α)
   claim₀ : ∀(α' : Baire) → α ≡[ s ] α' → dialogue(φ(α i)) α ≡ dialogue(φ(α i)) α'
   claim₀ = π₁(IH i α)
   claim₁ : ∀(α' : Baire) → α i ≡ α' i → dialogue (φ (α i)) α' ≡ dialogue (φ (α' i)) α'
   claim₁ α' r = cong (λ n → dialogue (φ n) α') r
   lemma : ∀(α' : Baire) → α ≡[ i ∷ s ] α'  → dialogue (φ(α i)) α ≡ dialogue(φ (α' i)) α'
   lemma α' (r ∷ rs) = trans (claim₀ α' rs) (claim₁ α' r)

continuity-extensional : ∀(f g : Baire → ℕ) → (∀(α : Baire) → f α ≡ g α) → continuous f → continuous g
continuity-extensional f g t c α = (π₀(c α) , (λ α' r → trans (sym (t α)) (trans (π₁(c α) α' r) (t α'))))

eloquent-is-continuous : ∀(f : Baire → ℕ) → eloquent f → continuous f
eloquent-is-continuous f (d , e) = continuity-extensional (dialogue d) f e (dialogue-continuity d)

\end{code}

Uniform continuity (still no difference):

\begin{code}

Cantor : Set
Cantor = ℕ → ℕ₂

C : Set → Set
C = D ℕ ℕ₂

data _≡[[_]]_ {X : Set} : (ℕ → X) → Tree ℕ → (ℕ → X) → Set where
  empty  : ∀{α α' : ℕ → X} → α ≡[[ empty ]] α'
  branch : ∀{α α' : ℕ → X} {i : ℕ} {s : ℕ₂ → Tree ℕ}
         → α i ≡ α' i → (∀(j : ℕ₂) → α ≡[[ s j ]] α') → α ≡[[ branch i s ]] α'

uniformly-continuous : (Cantor → ℕ) → Set
uniformly-continuous f = Σ \(s : Tree ℕ) → ∀(α α' : Cantor) → α ≡[[ s ]] α' → f α ≡ f α'

dialogue-UC : ∀(d : C ℕ) → uniformly-continuous(dialogue d)
dialogue-UC (η n) = (empty , λ α α' n → refl)
dialogue-UC (β φ i) = (branch i s , lemma)
  where
    IH : ∀(j : ℕ₂) → uniformly-continuous(dialogue(φ j))
    IH j = dialogue-UC (φ j)
    s : ℕ₂ → Tree ℕ
    s j = π₀(IH j)
    claim : ∀ j α α' → α ≡[[ s j ]] α' → dialogue (φ j) α ≡ dialogue (φ j) α'
    claim j = π₁(IH j)
    lemma : ∀ α α' → α ≡[[ branch i s ]] α' → dialogue (φ (α i)) α ≡ dialogue (φ (α' i)) α'
    lemma α α' (branch r l) = trans fact₀ fact₁
      where
       fact₀ : dialogue (φ (α i)) α ≡ dialogue (φ (α' i)) α
       fact₀ = cong (λ j → dialogue(φ j) α) r
       fact₁ : dialogue (φ (α' i)) α ≡ dialogue (φ (α' i)) α'
       fact₁ = claim (α' i) α α' (l(α' i))

UC-extensional : ∀(f g : Cantor → ℕ) → (∀(α : Cantor) → f α ≡ g α)
               → uniformly-continuous f → uniformly-continuous g
UC-extensional f g t (u , c) = (u , (λ α α' r → trans (sym (t α)) (trans (c α α' r) (t α'))))

eloquent-is-UC : ∀(f : Cantor → ℕ) → eloquent f → uniformly-continuous f
eloquent-is-UC f (d , e) = UC-extensional (dialogue d) f e (dialogue-UC d)

\end{code}

Dialogue-tree restriction from Baire to Cantor (no difference):

\begin{code}

embed-ℕ₂-ℕ : ℕ₂ → ℕ
embed-ℕ₂-ℕ ₀ = zero
embed-ℕ₂-ℕ ₁ = succ zero

embed-C-B : Cantor → Baire
embed-C-B α = embed-ℕ₂-ℕ ∘ α

C-restriction : (Baire → ℕ) → (Cantor → ℕ)
C-restriction f = f ∘ embed-C-B

prune : B ℕ → C ℕ
prune (η n) = η n
prune (β φ i) = β (λ j → prune(φ(embed-ℕ₂-ℕ j))) i

prune-behaviour : ∀(d : B ℕ) (α : Cantor) → dialogue (prune d) α ≡ C-restriction(dialogue d) α
prune-behaviour (η n)   α = refl
prune-behaviour (β φ n) α = prune-behaviour (φ(embed-ℕ₂-ℕ(α n))) α

eloquent-restriction : ∀(f : Baire → ℕ) → eloquent f → eloquent(C-restriction f)
eloquent-restriction f (d , c) = (prune d , λ α → trans (prune-behaviour d α) (c (embed-C-B α)))

\end{code}

System T types:

\begin{code}

data type : Set where
 ι    : type
 _⇒_ : type → type → type

infixr 6 _⇒_

\end{code}

It is here that the treatment differs from the references given above.

The set of system T terms of type σ in the context Γ is written T Γ σ.
A term with no free variables, that is, a closed term, lives in the
set T₀ σ = T 〈〉 σ, where 〈〉 is the empty context, defined above.

\begin{code}

Cxt : ℕ → Set
Cxt n = type ^ n

data T : {n : ℕ} (Γ : Cxt n) (σ : type) → Set where
 Zero : {n : ℕ}{Γ : Cxt n} → T Γ ι
 Succ : {n : ℕ}{Γ : Cxt n} → T Γ (ι ⇒ ι)
 Rec  : {n : ℕ}{Γ : Cxt n} → {σ : type}   → T Γ ((ι ⇒ σ ⇒ σ) ⇒ σ ⇒ ι ⇒ σ)
 ν    : {n : ℕ}{Γ : Cxt n} → (i : Fin n)  → T Γ (Γ [ i ])
 ƛ    : {n : ℕ}{Γ : Cxt n} → {σ τ : type} → T (Γ ’ σ) τ → T Γ (σ ⇒ τ)
 _·_  : {n : ℕ}{Γ : Cxt n} → {σ τ : type} → T Γ (σ ⇒ τ) → T Γ σ → T Γ τ

infixl 6 _·_

\end{code}

Notice that we have one variable ν i for each i : Fin n. (Here ν is
not the Roman letter vee but rather the Greek letter nu).

The standard interpretation of system T:

\begin{code}

〖_〗 : type → Set
〖 ι 〗 = ℕ
〖 σ ⇒ τ 〗 = 〖 σ 〗 → 〖 τ 〗

【_】 : {n : ℕ} (Γ : Cxt n) → Set
【 Γ 】 = (i : Fin _) → 〖 Γ [ i ] 〗

⟨⟩ : 【 〈〉 】
⟨⟩ ()

_‚_ : {n : ℕ} {Γ : Cxt n} {σ : type} → 【 Γ 】 → 〖 σ 〗 → 【 Γ ’ σ 】
(xs ‚ x) zero = x
(xs ‚ x) (succ i) = xs i

infixl 6 _‚_

⟦_⟧ : {n : ℕ} {Γ : Cxt n} {σ : type} → T Γ σ → 【 Γ 】 → 〖 σ 〗
⟦ Zero  ⟧  _ = zero
⟦ Succ  ⟧  _ = succ
⟦ Rec   ⟧  _ = rec
⟦ ν i   ⟧ xs = xs i
⟦ ƛ t   ⟧ xs = λ x → ⟦ t ⟧ (xs ‚ x)
⟦ t · u ⟧ xs = (⟦ t ⟧ xs) (⟦ u ⟧ xs)

\end{code}

Closed terms can be interpreted in a special way:

\begin{code}

T₀ : type → Set
T₀ = T 〈〉

⟦_⟧₀  : {σ : type} → T₀ σ → 〖 σ 〗
⟦ t ⟧₀ = ⟦ t ⟧ ⟨⟩

T-definable : ∀{σ : type} → 〖 σ 〗 → Set
T-definable x = Σ \t → ⟦ t ⟧₀ ≡ x

\end{code}

System T extended with a formal oracle Ω, called T' (rather than TΩ as previously):

\begin{code}

data T' : {n : ℕ} (Γ : Cxt n) (σ : type) → Set where
 Ω    : {n : ℕ}{Γ : Cxt n} → T' Γ (ι ⇒ ι)
 Zero : {n : ℕ}{Γ : Cxt n} → T' Γ ι
 Succ : {n : ℕ}{Γ : Cxt n} → T' Γ (ι ⇒ ι)
 Rec  : {n : ℕ}{Γ : Cxt n} → {σ : type}   → T' Γ ((ι ⇒ σ ⇒ σ) ⇒ σ ⇒ ι ⇒ σ)
 ν    : {n : ℕ}{Γ : Cxt n} → (i : Fin n)  → T' Γ (Γ [ i ])
 ƛ    : {n : ℕ}{Γ : Cxt n} → {σ τ : type} → T' (Γ ’ σ) τ → T' Γ (σ ⇒ τ)
 _·_  : {n : ℕ}{Γ : Cxt n} → {σ τ : type} → T' Γ (σ ⇒ τ) → T' Γ σ → T' Γ τ


⟦_⟧' : {n : ℕ} {Γ : Cxt n} {σ : type} → T' Γ σ → Baire → 【 Γ 】 → 〖 σ 〗
⟦ Ω     ⟧' α _ = α
⟦ Zero  ⟧' _  _ = zero
⟦ Succ  ⟧' _  _ = succ
⟦ Rec   ⟧' _  _ = rec
⟦ ν i   ⟧' _ xs = xs i
⟦ ƛ t   ⟧' α xs = λ x → ⟦ t ⟧' α (xs ‚ x)
⟦ t · u ⟧' α xs = (⟦ t ⟧' α xs) (⟦ u ⟧' α xs)

\end{code}

To regard system T as a sublanguage of T', we need to work with an
explicit embedding:

\begin{code}

embed : {n : ℕ} {Γ : Cxt n} {σ : type} → T Γ σ → T' Γ σ
embed Zero = Zero
embed Succ = Succ
embed Rec = Rec
embed (ν i) = ν i
embed (ƛ t) = ƛ(embed t)
embed (t · u) = (embed t) · (embed u)

\end{code}

Auxiliary definitions regarding the B constructor, used to define the
auxiliary interpretation of system T (this is as in the original
development cited above):

\begin{code}

kleisli-extension : ∀{X Y : Set} → (X → B Y) → B X → B Y
kleisli-extension f (η x)   = f x
kleisli-extension f (β φ i) = β (λ j → kleisli-extension f (φ j)) i

B-functor : ∀{X Y : Set} → (X → Y) → B X → B Y
B-functor f = kleisli-extension(η ∘ f)

decode : ∀{X : Set} → Baire → B X → X
decode α d = dialogue d α

decode-α-is-natural : ∀{X Y : Set}(g : X → Y)(d : B X)(α : Baire) → g(decode α d) ≡ decode α (B-functor g d)
decode-α-is-natural g (η x)   α = refl
decode-α-is-natural g (β φ i) α = decode-α-is-natural g (φ(α i)) α

decode-kleisli-extension : ∀{X Y : Set}(f : X → B Y)(d : B X)(α : Baire)
                         → decode α (f(decode α d)) ≡ decode α (kleisli-extension f d)
decode-kleisli-extension f (η x)   α = refl
decode-kleisli-extension f (β φ i) α = decode-kleisli-extension f (φ(α i)) α

\end{code}

Auxiliary interpretation of types:

\begin{code}

B〖_〗 : type → Set
B〖 ι 〗 = B(〖 ι 〗)
B〖 σ ⇒ τ 〗 = B〖 σ 〗 → B〖 τ 〗

\end{code}

Generalized Kleisli extension (as in the original treatment):

\begin{code}

Kleisli-extension : ∀{X : Set} {σ : type} → (X → B〖 σ 〗) → B X → B〖 σ 〗
Kleisli-extension {X} {ι} = kleisli-extension
Kleisli-extension {X} {σ ⇒ τ} = λ g d s → Kleisli-extension {X} {τ} (λ x → g x s) d

\end{code}

The interpretation of the system T constants (again as in the original
development):

\begin{code}

generic : B ℕ → B ℕ
generic = kleisli-extension(β η)

generic-diagram : ∀(α : Baire)(d : B ℕ) → α(decode α d) ≡ decode α (generic d)
generic-diagram α (η n) = refl
generic-diagram α (β φ n) = generic-diagram α (φ(α n))

zero' : B ℕ
zero' = η zero

succ' : B ℕ → B ℕ
succ' = B-functor succ

rec' : ∀{σ : type} → (B ℕ → B〖 σ 〗 → B〖 σ 〗) → B〖 σ 〗 → B ℕ → B〖 σ 〗
rec' f x = Kleisli-extension(rec (f ∘ η) x)

\end{code}

The auxiliary interpretation of contexts (which were not present in
the original development):

\begin{code}

B【_】 : {n : ℕ} (Γ : Cxt n) → Set
B【 Γ 】 = (i : Fin _) → B〖 Γ [ i ] 〗

⟪⟫ : B【 〈〉 】
⟪⟫ ()

_‚‚_ : {n : ℕ} {Γ : Cxt n} {σ : type} → B【 Γ 】 → B〖 σ 〗 → B【 Γ ’ σ 】
(xs ‚‚ x) zero = x
(xs ‚‚ x) (succ i) = xs i

\end{code}

The auxiliary interpretation of system T terms:

\begin{code}

B⟦_⟧ : {n : ℕ} {Γ : Cxt n} {σ : type} → T' Γ σ → B【 Γ 】 → B〖 σ 〗
B⟦ Ω     ⟧ _ = generic
B⟦ Zero  ⟧ _ = zero'
B⟦ Succ  ⟧ _ = succ'
B⟦ Rec   ⟧ _ = rec'
B⟦ ν i   ⟧ xs = xs i
B⟦ ƛ t   ⟧ xs = λ x → B⟦ t ⟧ (xs ‚‚ x)
B⟦ t · u ⟧ xs = (B⟦ t ⟧ xs) (B⟦ u ⟧ xs)

\end{code}

The dialogue tree of a closed term of type ((ι ⇒ ι) ⇒ ι):

\begin{code}

dialogue-tree : T₀((ι ⇒ ι) ⇒ ι) → B ℕ
dialogue-tree t = B⟦ (embed t) · Ω ⟧ ⟪⟫

\end{code}

The remainder of the development is the formulation and proof of the
correctness of the dialogue-tree function.

\begin{code}

preservation : {n : ℕ} {Γ : Cxt n} {σ : type} (t : T Γ σ) (α : Baire) → ⟦ t ⟧ ≡ ⟦ embed t ⟧' α
preservation Zero    α = refl
preservation Succ    α = refl
preservation Rec     α = refl
preservation (ν i)   α = refl
preservation (ƛ t)   α = cong (λ f → λ xs x → f(xs ‚ x)) (preservation t α)
preservation (t · u) α = cong₂ (λ f g x → f x (g x)) (preservation t α) (preservation u α)

\end{code}

The logical relation is the same as in the original development:

\begin{code}

R : ∀{σ : type} → (Baire → 〖 σ 〗) → B〖 σ 〗 → Set
R {ι} n n' =  ∀(α : Baire) → n α ≡ decode α n'
R {σ ⇒ τ} f f' = ∀(x : Baire → 〖 σ 〗) (x' : B〖 σ 〗) → R {σ} x x' → R {τ} (λ α → f α (x α)) (f' x')

\end{code}

The following lemma is again the same as in the original development,
by induction on types:

\begin{code}

R-kleisli-lemma : ∀(σ : type) (g : ℕ → Baire → 〖 σ 〗) (g' : ℕ → B〖 σ 〗)
  → (∀(k : ℕ) → R (g k) (g' k))
  → ∀(n : Baire → ℕ)(n' : B ℕ) → R n n' → R (λ α → g (n α) α) (Kleisli-extension g' n')

R-kleisli-lemma ι g g' rg n n' rn = λ α → trans (fact₃ α) (fact₀ α)
  where
    fact₀ : ∀ α → decode α (g' (decode α n')) ≡ decode α (kleisli-extension g' n')
    fact₀ = decode-kleisli-extension g' n'
    fact₁ : ∀ α → g (n α) α ≡ decode α (g'(n α))
    fact₁ α = rg (n α) α
    fact₂ : ∀ α → decode α (g' (n α)) ≡ decode α (g' (decode α n'))
    fact₂ α = cong (λ k → decode α (g' k)) (rn α)
    fact₃ : ∀ α → g (n α) α ≡ decode α (g' (decode α n'))
    fact₃ α = trans (fact₁ α) (fact₂ α)

R-kleisli-lemma (σ ⇒ τ) g g' rg n n' rn
  = λ y y' ry → R-kleisli-lemma τ (λ k α → g k α (y α)) (λ k → g' k y') (λ k → rg k y y' ry) n n' rn

\end{code}

The main lemma is a modification of the main lemma in the original
development, still by induction on terms. We don't have cases for the
combinators K and S anymore, but we need to add two cases for ν and ƛ,
and we need to modify the case for application _·_, which becomes more
difficult (in a routine way).  Additionally, we first need to extend R
to contexts (in the obvious way):

\begin{code}

Rs : ∀{n : ℕ} {Γ : Cxt n} → (Baire → 【 Γ 】) → B【 Γ 】 → Set
Rs {n} {Γ} xs ys = ∀(i : Fin n) → R {Γ [ i ]} (λ α → xs α i) (ys i)

main-lemma : ∀{n : ℕ} {Γ : Cxt n} {σ : type} (t : T' Γ σ) (xs : Baire → 【 Γ 】)(ys : B【 Γ 】)
          → Rs {n} {Γ} xs ys → R (λ α → ⟦ t ⟧' α (xs α)) (B⟦ t ⟧ ys)

main-lemma Ω xs ys cr = lemma
  where
    claim : ∀ α n n' → n α ≡ dialogue n' α → α(n α) ≡ α(decode α n')
    claim α n n' s = cong α s
    lemma : ∀(n : Baire → ℕ)(n' : B ℕ) → (∀ α → n α ≡ decode α n')
          → ∀ α → α(n α) ≡ decode α (generic n')
    lemma n n' rn α = trans (claim α n n' (rn α)) (generic-diagram α n')

main-lemma Zero xs ys cr = λ α → refl

main-lemma Succ xs ys cr = lemma
  where
    claim : ∀ α n n' → n α ≡ dialogue n' α → succ(n α) ≡ succ(decode α n')
    claim α n n' s = cong succ s
    lemma : ∀(n : Baire → ℕ)(n' : B ℕ) → (∀ α → n α ≡ decode α n')
          → ∀(α : Baire) → succ (n α) ≡ decode α (B-functor succ n')
    lemma n n' rn α = trans (claim α n n' (rn α)) (decode-α-is-natural succ n' α)

main-lemma (Rec {_} {_} {σ}) _ _ _ = lemma
  where
    lemma : ∀(f : Baire → ℕ → 〖 σ 〗 → 〖 σ 〗)(f' : B ℕ → B〖 σ 〗 → B〖 σ 〗) → R {ι ⇒ σ ⇒ σ} f f'
      → ∀(x : Baire → 〖 σ 〗)(x' : B〖 σ 〗)
      → R {σ} x x' → ∀(n : Baire → ℕ)(n' : B ℕ) → R {ι} n n'
      → R {σ} (λ α → rec (f α) (x α) (n α)) (Kleisli-extension(rec (f' ∘ η) x') n')
    lemma f f' rf x x' rx = R-kleisli-lemma σ g g' rg
       where
         g : ℕ → Baire → 〖 σ 〗
         g k α = rec (f α) (x α) k
         g' : ℕ → B〖 σ 〗
         g' k = rec (f' ∘ η) x' k
         rg : ∀(k : ℕ) → R (g k) (g' k)
         rg zero = rx
         rg (succ k) = rf (λ α → k) (η k) (λ α → refl) (g k) (g' k) (rg k)

main-lemma (ν i) xs ys cr = cr i

main-lemma {n} {Γ} {σ ⇒ τ} (ƛ t) xs ys cr = IH
  where
    IH : (x : Baire → 〖 σ 〗) (y : B〖 σ 〗)
        → R x y → R (λ α → ⟦ t ⟧' α (xs α ‚ x α)) (B⟦ t ⟧ (ys ‚‚ y))
    IH x y r = main-lemma t (λ α → xs α ‚ x α) (ys ‚‚ y) h
      where
        h : (i : Fin (succ n)) → R (λ α → (xs α ‚ x α) i) ((ys ‚‚ y) i)
        h zero = r
        h (succ i) = cr i

main-lemma (t · u) xs ys cr = IH-t (λ α → ⟦ u ⟧' α (xs α)) (B⟦ u ⟧ ys) IH-u
  where
    IH-t : (x : Baire → 〖 _ 〗) (x' : B〖 _ 〗)
         → R x x' → R (λ α → ⟦ t ⟧' α (xs α) (x α)) (B⟦ t ⟧ ys x')
    IH-t = main-lemma t xs ys cr
    IH-u : R (λ α → ⟦ u ⟧' α (xs α)) (B⟦ u ⟧ ys)
    IH-u = main-lemma u xs ys cr

\end{code}

Of course, all we are interested in is the ground case of the
main-lemma for closed terms, but we needed to prove the general case
to get that, using a logical relation to have a suitable induction
hypothesis, as usual.

\begin{code}

main-closed-ground : ∀(t : T' 〈〉 ι) (α : Baire) → ⟦ t ⟧' α ⟨⟩ ≡ decode α (B⟦ t ⟧ ⟪⟫)
main-closed-ground t = main-lemma t (λ α → ⟨⟩) ⟪⟫ (λ())

\end{code}

Then the correctness of the dialogue-tree function follows directly:

\begin{code}

dialogue-tree-correct : ∀(t : T₀((ι ⇒ ι) ⇒ ι)) (α : Baire) → ⟦ t ⟧₀ α ≡ decode α (dialogue-tree t)
dialogue-tree-correct t α = trans (fact₁ t α) (fact₀ t α)
  where
    fact₀ : ∀(t : T₀((ι ⇒ ι) ⇒ ι)) (α : Baire) → ⟦ embed t ⟧' α ⟨⟩ α ≡ decode α (dialogue-tree t)
    fact₀ t = main-closed-ground((embed t) · Ω)

    fact₁ : ∀(t : T₀((ι ⇒ ι) ⇒ ι)) (α : Baire) → ⟦ t ⟧₀ α ≡ ⟦ embed t ⟧' α ⟨⟩ α
    fact₁ t α = cong (λ f → f ⟨⟩ α) (preservation t α)

\end{code}

The main theorem follows directly from this:

\begin{code}

eloquence-theorem : ∀(f : Baire → ℕ) → T-definable f → eloquent f
eloquence-theorem f (t , r) = (dialogue-tree t , lemma)
  where
    r' : ∀ α → ⟦ t ⟧ ⟨⟩ α ≡ f α
    r' α = cong (λ h → h α) r
    lemma :  ∀(α : ℕ → ℕ) → dialogue (dialogue-tree t) α ≡ f α
    lemma α = trans (sym (dialogue-tree-correct t α)) (r' α)

corollary₀ : ∀(f : Baire → ℕ) → T-definable f → continuous f
corollary₀ f d = eloquent-is-continuous f (eloquence-theorem f d)

corollary₁ : ∀(f : Baire → ℕ) → T-definable f → uniformly-continuous(C-restriction f)
corollary₁ f d = eloquent-is-UC (C-restriction f) (eloquent-restriction f (eloquence-theorem f d))

\end{code}
