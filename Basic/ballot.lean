import Mathlib
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Basic
open BigOperators
open Nat


-- Define the ballot type
-- ballot sum n represents a ballot sequence of lenght n with 1 appearing sum-times
inductive ballot : ℕ → ℕ → Type
| nil : ballot 0 0
| next_1 : Π {sum n : ℕ}, ballot sum n → ballot (sum + 1) (n + 1)
| next_minus1 : Π {sum n : ℕ}, ballot sum n → ballot sum (n + 1)
