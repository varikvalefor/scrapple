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
\newunicodechar{λ}{\ensuremath{\mathnormal\lambda}}
\newunicodechar{→}{\ensuremath{\mathnormal\rightarrow}}
\newunicodechar{⇒}{\ensuremath{\mathnormal\Rightarrow}}
\newunicodechar{⇐}{\ensuremath{\mathnormal\Leftarrow}}
\newunicodechar{∃}{\ensuremath{\mathnormal\exists}}
\newunicodechar{∈}{\ensuremath{\mathnormal\in}}
\newunicodechar{∉}{\ensuremath{\mathnormal\notin}}
\newunicodechar{⦃}{\ensuremath{\mathnormal{\lbrace\hspace{-0.3em}|}}}
\newunicodechar{⦄}{\ensuremath{\mathnormal{|\hspace{-0.3em}\rbrace}}}
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
open import Data.Fin
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
    _⊎_
  )
open import Data.Vec
  as 𝕍
  using (
    Vec
  )
open import Function
  using (
    _∘_;
    _$_
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
open import Data.Maybe
  as ??
  using (
    nothing;
    Maybe;
    just
  )
open import Data.Product
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
open import Relation.Nullary
  using (
    ¬_
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
open import Truthbrary.Data.Vec.Matrix
  as 𝕄
  using (
    𝕄
  )
open import Data.List.Relation.Unary.All
  using (
    All
  )
open import Relation.Binary.PropositionalEquality
  as _≡_
  using (
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
    words = sid 𝕃.[] 𝕃.[]

    module Veritas where
      vin : Strong → List $ Maybe Char → Set
      vin s xs = M 𝕃.take ⊎ Midju ⊎ M 𝕃.drop
        where
        M = λ f → ∃ $ λ n → 𝕃.map just s ≡ f n xs
        Midju = Σ (ℕ × ℕ) $ λ (n₁ , n₂) → k ≡ midju n₁ n₂ xs
          where
          k = nothing 𝕃.∷ 𝕃.map just s 𝕃.++ 𝕃.[ nothing ]
          midju = λ n₁ n₂ → 𝕃.take n₂ ∘ 𝕃.drop n₁

      ∈w : (xs : List $ Maybe Char)
         → (s : Strong)
         → vin s xs
         → ∃ $ (s ≡_) ∘ 𝕃.lookup (words xs)
      ∈w = {!!}

      w∈ : (xs : List $ Maybe Char)
         → (s : Strong)
         → ∃ $ (s ≡_) ∘ 𝕃.lookup (words xs)
         → vin s xs
      w∈ = {!!}

      xrt : ∀ {a} → {A : Set a}
          → (xs : List $ Maybe A)
          → (_ : (n₁ n₂ : ℕ)
               → (¬_
                   (_≡_
                     (𝕃.replicate 2 nothing)
                     (𝕃.take n₂ $ 𝕃.drop n₁ xs))))
          → (_≡_
              xs
              ((𝕃.concat ∘ 𝕃.intersperse 𝕃.[ nothing ])
                (𝕃.map (𝕃.map just) $ words xs)))
      xrt = {!!}

  words = words.words

  f : List $ Maybe Char → List Strong
  f = 𝕃.filter (ℕ._>?_ 1 ∘ 𝕃.length) ∘ words

  →++↓ : {m n : ℕ} → 𝕄 (Maybe Char) m n → List $ List $ Maybe Char
  →++↓ x = 𝕍→[𝕊] x 𝕃.++ 𝕍→[𝕊] (𝕍.transpose x)

  cumvla : Bode → List Strong
  cumvla = 𝕃.concat ∘ 𝕃.map f ∘ →++↓ ∘ Bode.sp₁

  module Veritas where
    ropas : (b : Bode)
          → (s : Strong)
          → 𝕃.length s ℕ.> 1
          → (i : Fin $ 𝕍.length $ Bode.sp b)
          → (n₁ n₂ : ℕ)
          → (_≡_
              (𝕃.map just s)
              ((𝕃.take n₂ ∘ 𝕃.drop n₁)
                (𝕍.toList $ 𝕍.lookup (Bode.sp₁ b) i)))
          → ∃ $ (s ≡_) ∘ 𝕃.lookup (cumvla b)
    ropas = {!!}

open cumvla
  using (
    cumvla
  )

module jmina where
  jmina : (b : Bode)
        → Fin $ Bode.w b
        → Fin $ Bode.h b
        → Fin $ Bode.nikelci b
        → Fin 2
        → Maybe Bode
  jmina = {!!}

record Scrapple (Valsi : Strong → Set) : Set
  where
  field
    bode : Bode
    roval : All Valsi $ cumvla bode

record ScrappleGame (V : Strong → Set)
                    (V? : Decidable V) : Set
  where
  field
    scrapple : Scrapple V

  open Scrapple scrapple
  open Bode (Scrapple.bode scrapple)

  jmina : Fin w
        → Fin h
        → Fin nikelci
        → Fin 2
        → ScrappleGame V V? ⊎ (Set Function.∋ {!!})
  jmina = {!!}
\end{code}
\end{document}
