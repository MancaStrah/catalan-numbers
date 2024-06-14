-- bijection for task 1

import Mathlib
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Basic
open BigOperators
open Nat

#check sub_add
#check Nat.le_refl
#check sub_add_cancel
#check Nat.sub_add_cancel
#check le_or_lt
#check Fin.sum_univ_eq_sum_range
#check Fin.mk
#check  Equiv.trans
#check add_comm
#check sub_lt_sub_right
#check add_lt_add_right
#check Fin.sum_univ_castSucc
#check add_lt_add_iff_right
#check add_left_neg

-- lema for simplification
lemma x_minus_plus_strict {x a : ℕ} (h : a < x) : x = (x - a) + a := by
rw[Nat.sub_add_cancel]
rw[Nat.lt_iff_le_and_ne] at h
exact h.left

lemma x_minus_plus {x a : ℕ} (h : a ≤ x) : x = (x - a) + a := by
rw[Nat.sub_add_cancel]
exact h


example{a b c : Nat} (h1 : a < b) : a + c < b + c :=
by
apply add_lt_add_right
exact h1

example {a b c : Nat} (h1 : a + c < b + c) : a  < b :=
by
apply Nat.add_lt_add_iff_right.mp h1

lemma lemma1{a z c : Nat} (h1 : a  < z) : (a + c ) - c < z := by
simp
exact h1



lemma extract_full_members {n m: Nat} {k : Fin n → Nat}  {xz : Fin (∑ i : Fin n, k i)}  :
 ∃ j : (Fin (n)) , ∃ m : Fin ( k  j), xz =( ∑ i1 : Fin j.val, k ( Fin.castLE (Fin.is_lt j) i1)) + m := by
induction n with
| zero =>
-- zero example is trivial, since Fin0 is empty
--rewrite x to x:fin 0
  have h_sum : ∑ i : Fin 0, k i = 0 := by simp;
  rw[h_sum] at xz
  -- x doesnt exist
  exfalso
  exact  Fin.elim0 xz

--for n>0, we try if x > k1 + ... + k(n-1). If it is, than m = x - k1 + ... + k(n-1)
-- if its not, than x ∈ Fin(k1 + .. + k(n-1)) and we can usee the induction hypotesis
| succ nn ih =>
  let  q := ∑ ii : Fin nn, k ( Fin.castLE (Fin.is_lt nn) ii) ;
  match le_or_lt q ( xz.val)  with
  |Or.inl q_leq_x =>
    --use Fin.ofNat nn as j:
    use Fin.mk nn (Nat.lt_succ_self nn)
    -- use x - q as m:

    have xz_le_sum : xz.val < ( ∑ i : Fin (succ nn), k i )  :=
        by
        simp

    have xz_q_q_le_sum_q : (xz.val -q) +q< ( ∑ i : Fin (succ nn), k i ) +q:= by
      --rw[sub_add_cancel xz.val q]
      sorry

    -- proof for: xz - q < k(nn)
    have x_minus_q_le_knn : xz.val - q < k (Fin.mk nn (Nat.lt_succ_self nn)) :=--(Fin.castLE (Nat.lt_succ_self nn) nn) :=
      by
      simp
      ring_nf
      sorry
      --apply add_lt_add_iff_right.mp  xz_q_q_le_sum_q




    use Fin.mk (xz-q) x_minus_q_le_knn

    -- converts ↑{ val := ↑x - q, isLt := x_minus_q_le_knn } to sth nicer
    ring_nf
    rw[add_comm]
    --                 ∑ i1 : Fin j.val, k ( Fin.castLE (Fin.is_lt j) i1))
    have stupid_lean : ∑ i : Fin nn, k (Fin.castLE (Fin.is_lt nn) i) = ∑ y : Fin nn, k (Fin.castLE (Fin.is_lt nn) y) := by
      congr
    rw[stupid_lean]
    congr

    sorry

  | Or.inr x_le_q =>
    sorry


def fin_to_product : Fin (∑ i : Fin n, k i) → Σ i : Fin n , Fin (k i) :=
sorry







def iso_fin_sum {n : Nat} {k : Fin n → Nat} :
Fin (∑ i : Fin n, k i) ≅ Σ i : Fin n , Fin (k i) := by
sorry
