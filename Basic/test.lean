
import Mathlib
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Basic
open BigOperators
open Nat

lemma lemma1 {n m: Nat} {k : Fin n → Nat}  {xz : Fin (∑ i : Fin n, k i)}  :
 ∃ j : (Fin (n)) , ∃ m : Fin ( k  j), xz =( ∑ i1 : Fin j.val, k ( Fin.castLE (Fin.is_lt j) i1)) + m := by
induction n with
| zero =>
  /-
  some code
  -/
  sorry

| succ nn ih =>
  let  q := ∑ ii : Fin nn, k ( Fin.castLE (Fin.is_lt nn) ii) ;
  match le_or_lt q ( xz.val)  with
  |Or.inl q_leq_x =>

    use Fin.mk nn (Nat.lt_succ_self nn)


    have x_minus_q_le_knn : xz - q < k (Fin.mk nn (Nat.lt_succ_self nn)):=
      by sorry

    use Fin.mk (xz-q) x_minus_q_le_knn

    ring_nf
    rw[add_comm]

    -- ∑ ii : Fin nn, k (Fin.castLE _ ↑↑ii) and ∑ x : Fin nn, k (Fin.castLE _ ↑↑x) are equal. How to prove that?
    -- this rewritte fails
    rw[sub_add_cancel]
    sorry

  | Or.inr x_le_q =>
    /-
  some code
  -/
    sorry



def dist_fin_sigma {k : Nat} {n : Fin k → Nat} :
  (i : Fin k) × Fin (n i) ≃ Fin (∑ i : Fin k, n i) := by
  induction k with
  | zero => dsimp; apply Equiv.equivOfIsEmpty
  | succ k H =>
    apply Equiv.trans
    apply Equiv.sigmaCongr (β₂ := ?mot) ?base ?fiber
    case mot =>
      exact λ o => Fin (n (match o with | none => k | some i => Fin.castSucc i))
    case base => exact finSuccEquivLast
    case fiber =>
      apply Fin.lastCases
      . simp; apply Equiv.refl
      . intro i; simp; apply Equiv.refl
    apply Equiv.trans
    refine sigmaOptionEquivSum
    simp
    apply Equiv.trans
    apply Equiv.sumComm
    apply Equiv.trans
    exact
      (Bifunctor.mapEquiv Sum
        ( @H (n ·.castSucc))
        ( Equiv.refl (Fin (n (Fin.last k)))))
    apply Equiv.trans
    apply finSumFinEquiv
    apply finCongr
    symm
    apply Fin.sum_univ_castSucc
