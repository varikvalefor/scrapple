\begin{code}
open import Function
  using (
    _$_
  )
open import Data.List
  using (
    List
  )
open import Truthbrary.Data.Strong
  using (
    Strong
  )
open import Data.List.Relation.Unary.All
  using (
    All
  )

Bode : Set
Bode = {!!}

cumvla : Bode → List Strong
cumvla = {!!}

Valsi : Strong → Set
Valsi = {!!}

record Scrapple : Set
  where
  field
    bode : Bode
    roval : All Valsi $ cumvla bode
\end{code}
