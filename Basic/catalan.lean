import Mathlib
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Basic
open BigOperators
open Nat

def catalan_number : Nat → Nat
| 0 => 1
| succ n => ∑ i : Fin (succ n), (catalan_number i) * (catalan_number (n - i))

--what is Fin:
inductive Fin1 : Nat → Type
| zero : ∀ {n}, Fin1 (Nat.succ n)
| succ : ∀ {n}, Fin1 n → Fin1 (Nat.succ n)
