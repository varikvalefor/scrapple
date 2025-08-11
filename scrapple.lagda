\documentclass{article}

\usepackage{ar}
\usepackage[bw]{agda}
\usepackage{ifsym}
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{parskip}
\usepackage{mathabx}
\usepackage{fontspec}
\usepackage{unicode-math}
\usepackage{newunicodechar}

\newunicodechar{∷}{\ensuremath{\mathnormal\Colon}}
\newunicodechar{𝔽}{\ensuremath{\mathnormal{\mathbb F}}}
\newunicodechar{𝕃}{\ensuremath{\mathnormal{\mathbb L}}}
\newunicodechar{𝕄}{\ensuremath{\mathnormal{\mathbb 𝕄}}}
\newunicodechar{ℕ}{\ensuremath{\mathnormal{\mathbb N}}}
\newunicodechar{𝕊}{\ensuremath{\mathnormal{\mathbb S}}}
\newunicodechar{𝕍}{\ensuremath{\mathnormal{\mathbb V}}}
\newunicodechar{ℤ}{\ensuremath{\mathnormal{\mathbb Z}}}
\newunicodechar{ℚ}{\ensuremath{\mathnormal{\mathbb Q}}}
\newunicodechar{∘}{\ensuremath{\mathnormal\circ}}
\newunicodechar{∀}{\ensuremath{\mathnormal\forall}}
\newunicodechar{⊤}{\ensuremath{\mathnormal\top}}
\newunicodechar{⊥}{\ensuremath{\mathnormal\bot}}
\newunicodechar{λ}{\ensuremath{\mathnormal\lambda}}
\newunicodechar{→}{\ensuremath{\mathnormal\rightarrow}}
\newunicodechar{⇒}{\ensuremath{\mathnormal\Rightarrow}}
\newunicodechar{⇐}{\ensuremath{\mathnormal\Leftarrow}}
\newunicodechar{∃}{\ensuremath{\mathnormal\exists}}
\newunicodechar{∈}{\ensuremath{\mathnormal\in}}
\newunicodechar{∉}{\ensuremath{\mathnormal\notin}}
\newunicodechar{⦃}{\ensuremath{\mathnormal{\lbrace\hspace{-0.3em}|}}}
\newunicodechar{⦄}{\ensuremath{\mathnormal{|\hspace{-0.3em}\rbrace}}}
\newunicodechar{ₐ}{\ensuremath{\mathnormal{_\AgdaFontStyle{a}}}}
\newunicodechar{ᵢ}{\ensuremath{\mathnormal{_\AgdaFontStyle{i}}}}
\newunicodechar{ₗ}{\ensuremath{\mathnormal{_\AgdaFontStyle{l}}}}
\newunicodechar{ₛ}{\ensuremath{\mathnormal{_\AgdaFontStyle{s}}}}
\newunicodechar{ᵥ}{\ensuremath{\mathnormal{_\AgdaFontStyle{v}}}}
\newunicodechar{ₒ}{\ensuremath{\mathnormal{_\AgdaFontStyle{o}}}}
\newunicodechar{ᵇ}{\ensuremath{\mathnormal{^\AgdaFontStyle{b}}}}
\newunicodechar{ʳ}{\ensuremath{\mathnormal{^\AgdaFontStyle{r}}}}
\newunicodechar{ᵘ}{\ensuremath{\mathnormal{^\AgdaFontStyle{u}}}}
\newunicodechar{₋}{\ensuremath{\mathnormal{_-}}}
\newunicodechar{₁}{\ensuremath{\mathnormal{_1}}}
\newunicodechar{₂}{\ensuremath{\mathnormal{_2}}}
\newunicodechar{₃}{\ensuremath{\mathnormal{_3}}}
\newunicodechar{⊎}{\ensuremath{\mathnormal\uplus}}
\newunicodechar{≡}{\ensuremath{\mathnormal\equiv}}
\newunicodechar{≢}{\ensuremath{\mathnormal\nequiv}}
\newunicodechar{≗}{\ensuremath{\mathnormal\circeq}}
\newunicodechar{∧}{\ensuremath{\mathnormal\land}}
\newunicodechar{≤}{\ensuremath{\mathnormal\leq}}
\newunicodechar{∋}{\ensuremath{\mathnormal\ni}}
\newunicodechar{ₘ}{\ensuremath{\mathnormal{_m}}}
\newunicodechar{≟}{\ensuremath{\mathnormal{\stackrel{?}{=}}}}
\newunicodechar{∸}{\ensuremath{\mathnormal\divdot}}
\newunicodechar{∎}{\ensuremath{\mathnormal\blacksquare}}
\newunicodechar{⟨}{\ensuremath{\mathnormal\langle}}
\newunicodechar{⟩}{\ensuremath{\mathnormal\rangle}}
\newunicodechar{𝓁}{\ensuremath{\mathnormal{\mathcal l}}}
\newunicodechar{ℓ}{\ensuremath{\mathnormal\ell}}
\newunicodechar{χ}{\ensuremath{\mathnormal\chi}}
\newunicodechar{⊃}{\ensuremath{\mathnormal\supset}}
\newunicodechar{⊆}{\ensuremath{\mathnormal\subseteq}}
\newunicodechar{⊑}{\ensuremath{\mathnormal\sqsubseteq}}
\newunicodechar{▹}{\ensuremath{\mathnormal\triangleright}}
\newunicodechar{⊔}{\ensuremath{\mathnormal\sqcup}}
\newunicodechar{⊓}{\ensuremath{\mathnormal\sqcap}}
\newunicodechar{⟲}{\ensuremath{\mathnormal\circlearrowleft}}
\newunicodechar{𝓫}{\ensuremath{\mathnormal{\mathcal b}}}
\newunicodechar{𝓰}{\ensuremath{\mathnormal{\mathcal g}}}
\newunicodechar{𝓵}{\ensuremath{\mathnormal{\mathcal l}}}

\newfontface{\ayyplcihartai}{APL333}
\DeclareTextFontCommand{\ayypl}{\ayyplcihartai}
\newunicodechar{⌽}{\ensuremath{\ayypl ⌽}}
\newunicodechar{⍨}{\ensuremath{\ayypl ⍨}}

\newcommand\Sym\AgdaSymbol
\newcommand\D\AgdaDatatype
\newcommand\F\AgdaFunction
\newcommand\B\AgdaBound
\newcommand\IC\AgdaInductiveConstructor
\newcommand\OpF[1]{\AgdaOperator{\F{#1}}}

\newcommand\sds{\spacefactor\sfcode`.\ \space}

\newcommand\Xr[2]{\textrm{#1(#2)}}
\newcommand\datnyveicme\texttt

\title{la'oi zoi.\ \datnyveicme{Scrapple}\ .zoi.}
\author{la .varik.\ .VALefor.}

\begin{document}
\maketitle
\begin{code}
open import Level
  using (
    _⊔_
  )
open import Data.Fin
  as 𝔽
  using (
    Fin
  )
open import Data.Nat
  as ℕ
  using (
    ℕ
  )
open import Data.Sum
  as _⊎_
  using (
    inj₂;
    _⊎_
  )
open import Data.Vec
  as 𝕍
  using (
    Vec
  )
open import Function
  using (
    _∋_;
    _∘_;
    _$_
  )
  renaming (
    _|>_ to _▹_;
    flip to _⍨
  )
open import Data.Bool
  using (
  )
  renaming (
    if_then_else_ to if
  )
open import Data.Char
  using (
    Char
  )
open import Data.List
  as 𝕃
  using (
    List
  )
  renaming (
    reverse to ⌽
  )
open import Data.Empty
  using (
    ⊥-elim
  )
open import Data.Maybe
  as ??
  using (
    nothing;
    Maybe;
    just
  )
open import Data.Product
  as Σ
  using (
    proj₁;
    _×_;
    _,_;
    Σ;
    ∃
  )
open import Relation.Unary
  using (
    Decidable
  )
open import Relation.Binary
  using (
  )
  renaming (
    Decidable to Decidable₂
  )
open import Relation.Nullary
  using (
    Dec;
    yes;
    ¬_;
    no
  )
open import Agda.Builtin.Unit
  as ABu
  using (
  )
open import Truthbrary.Data.Fin
  using (
    mink
  )
open import Truthbrary.Record.Eq
  using (
    _≟_
  )
open import Truthbrary.Record.LLC
  using (
    _∈_
  )
open import Truthbrary.Data.Strong
  as 𝕊
  using (
    Strong
  )
open import Relation.Nullary.Decidable
  using (
    dec-no
  )
open import Truthbrary.Data.Vec.Matrix
  as 𝕄
  using (
    𝕄
  )
open import Data.List.Relation.Unary.All
  using (
    All
  )
open import Data.Maybe.Relation.Unary.Any
  as DMRUA
  using (
  )
open import Data.Maybe.Relation.Unary.All
  as DMRU∀
  using (
  )
open import Relation.Binary.PropositionalEquality
  as _≡_
  using (
    cong;
    refl;
    sym;
    _≡_
  )
\end{code}

\begin{code}
record Bode : Set
  where
  field
    nikelci : ℕ
    w : ℕ
    h : ℕ
  D = Char × Fin nikelci
  field
    sp : 𝕄 (Maybe D) w h
  sp₁ = 𝕍.map (𝕍.map $ ??.map proj₁) sp
\end{code}

\section{la .\F{cumvla}.}
ni'o ro da zo'u ro de zo'u ga jo da cmima lo me'oi .\F{cumvla}.\ be de gi ga je da co'e ja pagbu pe'a lo me'oi .board.\ gi ga naje .indika gi cumki fa lo nu da valsi
    
\begin{code}
module cumvla where
  𝕍→[𝕊] : ∀ {a} → {A : Set a}
        → {m n : ℕ}
        → 𝕄 A m n
        → List $ List $ A
  𝕍→[𝕊] = 𝕍.toList ∘ 𝕍.map 𝕍.toList

  module words where
    sid : ∀ {a} → {A : Set a}
        → List $ List A
        → List A
        → List $ Maybe A
        → List $ List A
    sid x b (nothing 𝕃.∷ is) = sid (⌽ b 𝕃.∷ x) 𝕃.[] is
    sid x b (just i 𝕃.∷ is) = sid x (i 𝕃.∷ b) is
    sid x b 𝕃.[] = ⌽ $ ⌽ b 𝕃.∷ x

    words : ∀ {a} → {A : Set a} → List $ Maybe A → List $ List A
    words = 𝕃.filter ((0 ℕ.<?_) ∘ 𝕃.length) ∘ sid 𝕃.[] 𝕃.[]

    module Veritas where
      vin : Strong → List $ Maybe Char → Set
      vin s xs = M 𝕃.take ⊎ Midju ⊎ M 𝕃.drop
        where
        M = λ f → ∃ $ λ n → 𝕃.map just s ≡ f n xs
        Midju = Σ (_ × _) $ (k ≡_) ∘ Σ.uncurry (midju xs)
          where
          k = nothing 𝕃.∷ 𝕃.map just s 𝕃.++ 𝕃.[ nothing ]
          midju = λ xs n₁ n₂ → 𝕃.take n₂ $ 𝕃.drop n₁ xs

      >→¬vin : (v : Strong)
             → (l : List $ Maybe Char)
             → 𝕃.length v ℕ.> 𝕃.length l
             → ¬_ $ vin v l
      >→¬vin v l z (_⊎_.inj₁ c) = {!!}
      >→¬vin v l z (inj₂ (_⊎_.inj₁ c)) = {!!}
      >→¬vin v l z (inj₂ (inj₂ c)) = {!!}

      vin→S : (v : Strong)
            → (l : List $ Maybe Char)
            → ¬_ $ v ≡ 𝕃.[]
            → vin v l
            → ∃ $ λ n → 𝕃.length (words l) ≡ ℕ.suc n
      vin→S 𝕃.[] _ N _ = ⊥-elim $ N refl
      vin→S = {!!}

      romidjus : (v : Strong)
               → (l : List $ Maybe Char)
               → (c : vin v l)
               → (_⊎_
                   (∃ $ λ x → c ≡ _⊎_.inj₁ x)
                   (∃ $ λ x → c ≡ inj₂ (inj₂ x)))
               → (Σ
                   (vin v l)
                   (λ c₂ →
                     (∃ $ λ x → c₂ ≡ inj₂ (_⊎_.inj₁ x))))
      romidjus = {!!}

      kunti :  ∀ {a} → {A : Set a}
            → words {A = A} 𝕃.[] ≡ 𝕃.[]
      kunti = refl

      ∈w : (xs : List $ Maybe Char)
         → (s : Strong)
         → ¬_ $ s ≡ 𝕃.[]
         → vin s xs
         → ∃ $ (s ≡_) ∘ 𝕃.lookup (words xs)
      ∈w xs s z (_⊎_.inj₁ v) = coerce d Fin.zero , {!!}
        where
        d = vin→S s xs z (_⊎_.inj₁ v) ▹ Σ.proj₂ ▹ sym ▹ cong Fin
        coerce : ∀ {a} → {A B : Set a} → A ≡ B → A → B
        coerce refl x = x
      ∈w xs s z (inj₂ (_⊎_.inj₁ v)) = {!!}
      ∈w xs s z (inj₂ (inj₂ v)) = {!!}

      w∈ : (xs : List $ Maybe Char)
         → (s : Strong)
         → ∃ $ (s ≡_) ∘ 𝕃.lookup (words xs)
         → vin s xs
      w∈ 𝕃.[] s (() , d)
      w∈ (x 𝕃.∷ xs) s (f , d) = {!!}

      xrt : ∀ {a} → {A : Set a}
          → (xs : List $ Maybe A)
          → (_ : (n₁ : ℕ)
               → (¬_
                   (_≡_
                     (𝕃.replicate 2 nothing)
                     (𝕃.take 2 $ 𝕃.drop n₁ xs))))
          → (_≡_
              xs
              ((𝕃.concat ∘ 𝕃.intersperse 𝕃.[ nothing ])
                (𝕃.map (𝕃.map just) $ words xs)))
      xrt = {!!}

      >0 : (xs : List $ Maybe Char)
         → All (λ e → 𝕃.length e ℕ.> 0) $ words xs
      >0 = {!!}

  words = words.words

  →++↓ : {m n : ℕ} → 𝕄 (Maybe Char) m n → List $ List $ Maybe Char
  →++↓ x = 𝕍→[𝕊] x 𝕃.++ 𝕍→[𝕊] (𝕍.transpose x)

  cumvla : Bode → List Strong
  cumvla = 𝕃.concat ∘ 𝕃.map words ∘ →++↓ ∘ Bode.sp₁

  module Veritas where
    ropas : (b : Bode)
          → (s : Strong)
          → 𝕃.length s ℕ.> 1
          → ∃ $ words.Veritas.vin s ∘ 𝕍.toList ∘ 𝕍.lookup (Bode.sp₁ b)
          → ∃ $ (s ≡_) ∘ 𝕃.lookup (cumvla b)
    ropas = {!!}

    rores : (b : Bode)
          → (s : Strong)
          → 𝕃.length s ℕ.> 1
          → ∃ $ words.Veritas.vin s ∘ 𝕍.toList ∘ 𝕍.lookup (𝕍.transpose $ Bode.sp₁ b)
          → ∃ $ (s ≡_) ∘ 𝕃.lookup (cumvla b)
    rores = {!!}

    cumvla→vin : (b : Bode)
               → (s : Strong)
               → ∃ $ (s ≡_) ∘ 𝕃.lookup (cumvla b)
               → (_⊎_
                   (∃ $ words.Veritas.vin s ∘ 𝕍.toList ∘ 𝕍.lookup (Bode.sp₁ b))
                   (∃ $ words.Veritas.vin s ∘ 𝕍.toList ∘ 𝕍.lookup (𝕍.transpose $ Bode.sp₁ b)))
    cumvla→vin = {!!}

cumvla = cumvla.cumvla
\end{code}

\section{le me'oi .iteration.\ se ctaipe}

\begin{code}
module _⊑_ where
  lookup₂ : ∀ {a} → {A : Set a}
          → {m n : ℕ}
          → 𝕄 A m n
          → Fin m
          → Fin n
          → A
  lookup₂ = λ x f₁ f₂ → 𝕍.lookup (𝕍.lookup x f₂) f₁

  _⇒_ : ∀ {a b} → Set a → Set b → Set (a ⊔ b)
  _⇒_ X Z = Z ⊎ (¬ X)

  _⇒?_ : ∀ {a b} → (A : Set a) → (B : Set b)
       → {A? : Dec A}
       → {B? : Dec B}
       → Dec $ A ⇒ B
  _⇒?_ _ _ {B? = yes b} = yes $ _⊎_.inj₁ b
  _⇒?_ _ _ {yes cₐ} {no N} = no $ ⊥-elim ∘ _⊎_.[ N , _$ cₐ ]
  _⇒?_ _ _ {no Nₐ} {no N} = yes $ inj₂ Nₐ

  coords : {n₁ n₂ : ℕ} → List $ Fin n₁ × Fin n₂
  coords = 𝕃.cartesianProduct (𝕃.allFin _) $ 𝕃.allFin _

  -- | ni'o filri'a tu'a la'oi .Mapti.
  record M (b c : Bode) : Set where
    D : ∀ {a} → {A : Set a} → (Bode → A) → Set a
    D f = f b ≡ f c
    field
      wd : D Bode.w
      hd : D Bode.h
      kd : D Bode.nikelci

  M? : Decidable₂ M
  M? b c with _ ≟ _ | _ ≟ _ | _ ≟ _
  ... | no Nw | _ | _ = no $ Nw ∘ M.wd
  ... | _ | no Nh | _ = no $ Nh ∘ M.hd
  ... | _ | _ | no Nk = no $ Nk ∘ M.kd
  ... | yes w | yes h | yes k = yes $ record {wd = w; hd = h; kd = k}

  reler : (b₁ b₂ : Bode)
        → M b₁ b₂
        → Fin (Bode.w b₁) × Fin (Bode.h b₁)
        → Maybe Char × Maybe Char
  reler b₁ b₂ m (i₁ , i₂) = lookup₂ (Bode.sp₁ b₁) i₁ i₂ , lookup₂ (Bode.sp₁ b₂) i₁' i₂'
    where
    open M m
    i₁' = mink i₁ wd
    i₂' = mink i₂ hd

  Mapti : (b₁ b₂ : Bode)
        → M b₁ b₂
        → Fin (Bode.w b₁) × Fin (Bode.h b₁)
        → Set
  Mapti b₁ b₂ m (i₁ , i₂) = J ⇒ Dunli
    where
    open M m
    J = ??.Is-just $ lookup₂ (Bode.sp₁ b₁) i₁ i₂
    Dunli = Σ.uncurry _≡_ $ reler b₁ b₂ m $ i₁ , i₂

  Mapti? : (b₁ b₂ : Bode)
         → (m : M b₁ b₂)
         → Decidable $ Mapti b₁ b₂ m
  Mapti? _ _ _ _ = _⇒?_ _ _ {Is-just? _} {_ ≟ _}
    where
    Is-just? : ∀ {a} → {A : Set a} → Decidable $ ??.Is-just {A = A}
    Is-just? nothing = no $ λ ()
    Is-just? (just _) = yes $ DMRUA.just ABu.tt

  -- | ni'o ro da zo'u ro de zo'u ga jo ctaipe lo mu'oi
  -- zoi. _⊑_ .zoi. be da bei de gi ro di poi me da je de
  -- se zvati namcu pe'a zo'u lo di moi pe'a be da cu
  -- me'oi .nothing. jonai cu di moi pe'a de
  _⊑_ : Bode → Bode → Set
  _⊑_ b₁ b₂ = ∃ $ λ x → All (Mapti b₁ b₂ x) coords

  _⊑?_ : Decidable₂ _⊑_
  _⊑?_ b c with M? b c
  ... | no N = no $ N ∘ Σ.proj₁
  ... | yes M! with Data.List.Relation.Unary.All.all? Mapti?' _
    where
    Mapti?' = Mapti? b c M!
  ... | yes rov = yes $ M! , rov
  ... | no N = no $ λ x → ⊥-elim $ (_$ Σ.proj₂ x) $ _≡_.subst (λ x → ¬ M' x) {!!} N
    where
    M' = λ x → All (Mapti b c x) coords

  module Veritas where
    ⇒→→ : ∀ {a b} → {A : Set a} → {B : Set b}
        → A ⇒ B
        → A → B
    ⇒→→ (_⊎_.inj₁ x) x₁ = x
    ⇒→→ (inj₂ y) x₁ = ⊥-elim $ y x₁

    →→⇒ : ∀ {a b} → {A : Set a} → {B : Set b}
        → (A → B)
        → A ⇒ B
    →→⇒ = {!!}

    Mapti-nothing : (b₁ b₂ : Bode)
                  → (m : M b₁ b₂)
                  → (i₁ : Fin _)
                  → (i₂ : Fin _)
                  → nothing ≡ lookup₂ (Bode.sp₁ b₁) i₁ i₂
                  → Mapti b₁ b₂ m $ i₁ , i₂
    Mapti-nothing = λ b₁ b₂ m i₁ i₂ x → inj₂ $ N⇒¬J _ x
      where
      N⇒¬J : ∀ {a} → {A : Set a}
           → (x : Maybe A)
           → nothing ≡ x
           → ¬ ??.Is-just x
      N⇒¬J nothing refl ()

    Mapti-just : (b₁ b₂ : Bode)
               → (m : M b₁ b₂)
               → (i₁ : Fin _)
               → (i₂ : Fin _)
               → (c : Char)
               → Σ.uncurry _≡_ $ reler _ _ m $ i₁ , i₂
               → Mapti b₁ b₂ m $ i₁ , i₂
    Mapti-just = {!!}

    ¬Mapti : (b₁ b₂ : Bode)
           → (m : M b₁ b₂)
           → (i₁ : Fin _)
           → (i₂ : Fin _)
           → ??.Is-just $ lookup₂ (Bode.sp₁ b₁) i₁ i₂
           → ¬_ $ Σ.uncurry _≡_ $ reler _ _  m $ i₁ , i₂
           → ¬_ $ Mapti b₁ b₂ m $ i₁ , i₂
    ¬Mapti = {!!}

    xor : (b₁ b₂ : Bode)
        → (m : M b₁ b₂)
        → (i₁ : Fin _)
        → (i₂ : Fin _)
        → (_⊎_
            (¬_ $ Σ.uncurry _≡_ $ reler _ _  m $ i₁ , i₂)
            (_⊎_
              (nothing ≡ lookup₂ (Bode.sp₁ b₁) i₁ i₂)
              (Σ.uncurry _≡_ $ reler _ _ m $ i₁ , i₂)))
    xor b₁ b₂ m i₁ i₂ with Dec (??.Is-just $ lookup₂ (Bode.sp₁ b₁) i₁ i₂) ∋ {!!}
    ... | no N = inj₂ $ _⊎_.inj₁ $ ¬J⇒N N
      where
      ¬J⇒N : ∀ {a} → {A : Set a}
           → {x : Maybe A}
           → ¬ ??.Is-just x
           → nothing ≡ x
      ¬J⇒N {x = nothing} = λ _ → refl
      ¬J⇒N {x = just x} = ⊥-elim ∘ (_$ {!!})
    ... | yes j = {!!}

_⊑_ = _⊑_._⊑_

_⊑?_ = _⊑_._⊑?_
\end{code}

\section{le jmina pe'a fancu}

\begin{code}
module jmina where
  record JRq (b : Bode) : Set where
    field
      w : Fin $ Bode.w b
      h : Fin $ Bode.h b
      k : Fin $ Bode.nikelci b
      s : Strong
      d : Fin 2
      mapti-cmalu₀ : d ≡ Fin.zero
                   → (ℕ._<_
                       (𝔽.toℕ w ℕ.+ 𝕃.length s)
                       (Bode.w b))
      mapti-cmalu₁ : d ≡ Fin.suc Fin.zero
                   → (ℕ._<_
                       (𝔽.toℕ h ℕ.+ 𝕃.length s)
                       (Bode.h b))

  record Zabna {b : Bode} (j : JRq b) : Set where
    open JRq j
    field
      na-basti : (All
                   ??.Is-nothing
                   ((𝕃.take (𝕃.length s) ∘ 𝕃.drop (𝔽.toℕ w))
                     (𝕍.toList $ 𝕍.lookup (Bode.sp b) h)))

  Zabna? : {b : Bode} → Decidable $ Zabna {b}
  Zabna? x with Data.List.Relation.Unary.All.all? Is-nothing? _
    where
    Is-nothing? : ∀ {a} → {A : Set a} → Decidable $ ??.Is-nothing {A = A}
    Is-nothing? nothing = yes DMRU∀.nothing
    Is-nothing? (just x) = no {!!}
  ... | no N = no $ N ∘ Zabna.na-basti
  ... | yes r = yes $ record {na-basti = r}

  jmina! : (b : Bode) → JRq b → Bode
  jmina! b j = if (d Truthbrary.Record.Eq.≡ᵇ Fin.zero) x₀ x₁
    where
    coerce : ∀ {a} → {A B : Set a} → A ≡ B → A → B
    coerce refl x = x
    open JRq  j
    x₀ = record {
      nikelci = Bode.nikelci b;
      w = Bode.w b;
      h = Bode.h b;
      sp = coerce {!!} $ 𝕍.take (𝔽.toℕ w) (coerce {!!} $ Bode.sp b) 𝕍.++ {!!} 𝕍.++ 𝕍.drop (ℕ.suc $ 𝔽.toℕ w) (coerce {!!} $ Bode.sp b)
      }
    x₁ = {!!}

  jminan : (b : Bode)
         → (w : Fin $ Bode.w b)
         → (h : Fin $ Bode.h b)
         → (k : Fin $ Bode.nikelci b)
         → (d : Fin 2)
         → (s : Strong)
         → (_ : d ≡ Fin.zero
              → (_×_
                  (ℕ._<_
                    (𝔽.toℕ w ℕ.+ 𝕃.length s)
                    (Bode.w b))
                  (All
                    ??.Is-nothing
                    ((𝕃.take (𝕃.length s) ∘ 𝕃.drop (𝔽.toℕ w))
                      (𝕍.toList $ 𝕍.lookup (Bode.sp b) h)))))
         → (_ : d ≡ Fin.suc Fin.zero
              → Set ∋ {!!})
         → Set ∋ {!!}
         → Bode
  jminan = {!!}

  jmina : (b : Bode)
        → Fin $ Bode.w b
        → Fin $ Bode.h b
        → Fin $ Bode.nikelci b
        → Fin 2
        → Strong
        → Maybe Bode
  jmina = {!!}
\end{code}

\subsection{le ctaipe be le su'u mapti}

\begin{code}
  module Veritas where
    module dunli (b : Bode)
                 (w : _)
                 (h : _)
                 (k : _)
                 (d : _)
                 (s : _)
                 (J : ??.Is-just $ jmina b w h k d s) where

      b₂ : Bode
      b₂ = ??.to-witness J

      wd : Bode.w b ≡ Bode.w b₂
      wd = {!!}

      hd : Bode.h b ≡ Bode.h b₂
      hd = {!!}

      kd : Bode.nikelci b ≡ Bode.nikelci b₂
      kd = {!!}

    j⊑ : (b : Bode)
       → (w : _)
       → (h : _)
       → (k : _)
       → (d : _)
       → (s : _)
       → (J : ??.Is-just $ jmina b w h k d s)
       → b ⊑ ??.to-witness J
    j⊑ = {!!}
\end{code}

\section{la'oi .\AgdaRecord{Scrapple}.}
ni'o ga naja ko'a goi la'oi .\B{x}.\ ctaipe la'o zoi.\ \AgdaRecord{Scrapple} \B{V} .zoi.\ gi\ldots

\begin{itemize}
	\item ga je ko'a sinxa ko'e goi lo zazyfau pe lo valsi selkei gi
	\item ga je la'o zoi.\ \AgdaField{Scrapple.bode} \B{x}\ .zoi.\ sinxa lo keirta'o pe ko'e gi
	\item ga je la'o zoi.\ \AgdaField{Scrapple.lerste} \B{x}\ .zoi.\ liste lo'i ro lerfu poi curmi lo nu pilno ke'a ku'o no'u pe'a lo'i ro lerfu tapla je ke se vecnu\ldots ku'o je cu se klesi lo'i ro lerfu pe la'o zoi.\ \AgdaField{Scrapple.bode} \B{x}\ .zoi.\ gi
	\item la .varik.\ cu pacna lo nu na sarcu fa lo nu sikicu bau la .lojban.\ fe lo du'u mo kau la'o zoi.\ \AgdaField{Scrapple.roval}\ .zoi.
\end{itemize}

\begin{code}
record Scrapple (Valsi : Strong → Set) : Set
  where
  field
    bode : Bode
    lerste : Strong
    roval : All Valsi $ cumvla bode
\end{code}

\section{la'oi .\AgdaRecord{ScrappleGame}.}

\begin{code}
record ScrappleGame (V : Strong → Set)
                    (V? : Decidable V) : Set
  where
  field
    scrapple : Scrapple V

  open Scrapple scrapple
  open Bode (Scrapple.bode scrapple)

  data Exception : Set where
    Malvla : ∃ $ ¬_ ∘ V → Exception
    Bradu'e : {!!} → Exception

  module sgjmina (w : Fin w)
                 (h : Fin h)
                 (k : Fin nikelci)
                 (d : Fin 2)
                 (s : Strong) where

    f₁ : Dec $ V s → _
    f₁ (no N) = inj₂ $ Malvla $ s , N
    f₁ (yes v) = {!!}

    jmina : ScrappleGame V V? ⊎ (Set ∋ Exception)
    jmina = f₁ $ V? s

    module Veritas where
      ¬V-fliba : ¬ V s → ∃ $ _≡_ jmina ∘ inj₂
      ¬V-fliba sex = Malvla (s , proj₁ N) , dx
        where
        N = _⍨ dec-no sex _
        dx : _ ≡ _
        dx = begin
          jmina ≡⟨ refl ⟩
          f₁ (V? s) ≡⟨ (V? s ≡ _ ∋ Σ.proj₂ N) ▹ cong f₁ ⟩
          f₁ (no $ proj₁ N) ≡⟨ refl ⟩
          inj₂ (Malvla $ s , proj₁ N) ∎
          where
          open _≡_.≡-Reasoning

  jmina = sgjmina.jmina
\end{code}
\end{document}
