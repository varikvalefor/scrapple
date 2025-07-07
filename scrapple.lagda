\begin{code}
open import Data.Fin
  using (
    Fin
  )
open import Data.Nat
  using (
    ℕ
  )
open import Function
  using (
    _$_
  )
open import Data.Char
  using (
    Char
  )
open import Data.List
  using (
    List
  )
open import Data.Product
  using (
    _×_
  )
open import Relation.Unary
  using (
    Decidable
  )
open import Truthbrary.Data.Strong
  using (
    Strong
  )
open import Truthbrary.Data.Vec.Matrix
  using (
    𝕄
  )
open import Data.List.Relation.Unary.All
  using (
    All
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
    sp : 𝕄 D w h
\end{code}
    
\begin{code}
cumvla : Bode → List Strong
cumvla = {!!}

record Scrapple (Valsi : Strong → Set) : Set
  where
  field
    bode : Bode
    roval : All Valsi $ cumvla bode
\end{code}
