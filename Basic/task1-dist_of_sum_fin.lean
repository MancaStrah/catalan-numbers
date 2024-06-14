-- imports
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Functor
import Mathlib.Logic.Equiv.Defs
import Mathlib.Control.Bifunctor
import Mathlib.Logic.Equiv.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import Mathlib.Data.Nat.Order.Basic

open Nat
open Finset
open BigOperators
open Fin
#align_import algebra.big_operators.fin from "leanprover-community/mathlib"@"cc5dd6244981976cc9da7afc4eee5682b037a013"

-- IDEA
--there is finSumFinEquiv, which proves n= 2 for a similar structure (⊕ instead of Σ)
#check finSumFinEquiv
/-
We could prove  (  Σ i : Fin n , Fin ( k i) ) ≃  Fin (∑ i : Fin n, k i) with:
1. Prove
 ∑ i : Fin (succ n), k  =  Fin (k 1) ⊕ Fin (k 2) ⊕ ... ⊕ Fin (k n)
2. Use finSumFinEquiv to prove
 Fin (k 1) ⊕ Fin (k 2) ⊕ ... ⊕ Fin (k n) = Fin((k 1) + (k 2) + ... + (k n))
-/

/-
For step 1, we need to estavlish a connection between Σ and ⊕.

First, we need a type representing Fin (k 1) ⊕ Fin (k 2) ⊕ ... ⊕ Fin (k n):
-/
def sumOfFin : (n : Nat) → (k : Nat → Nat) → Type
  | 0, _ => PEmpty -- same as Fin 0
  | n + 1, k =>  (sumOfFin n (fun i => k (i))) ⊕ (Fin (k n))

-- alternative:
def RsumOfFin : (n : Nat) → (k : Nat → Nat) → Type
  | 0, _ => PEmpty
  | n + 1, k => Sum (Fin (k 0)) (sumOfFin n (fun i => k (Fin.succ i)))

-- EXAMPLE USAGE:
def kId (n : Nat) (x : Nat) : Nat := x
#reduce sumOfFin 4 (kId 4)
#reduce sumOfFin 0 (kId 0)


-- USEFUL LEMMAS

-- Equvivalence is a congruence for ⊕:
lemma sumCong (h: A ≃ B) : A ⊕ C ≃ B ⊕ C := by
  apply Equiv.sumCongr h
  apply Equiv.refl C

---------------------
-- STEP 1 - relation between Σ and ⊕
---------------------

k { val := n, isLt := _ }
--lemma lemma1 {k : ℕ → ℕ} (x : Fin k i) :

-- Define the forward direction function
def forward {n : ℕ} {k : ℕ → ℕ} :
  (Σ i : Fin (Nat.succ n), Fin (k i)) → (Σ i : Fin n, Fin (k i)) ⊕ Fin (k n) :=
fun ⟨i, x⟩ =>
  if h : i.val < n
  then Sum.inl ⟨Fin.castLT i h,  by
                        use x
                        simp
  ⟩
  else Sum.inr (by
  use  x
  sorry

  )

  def backward {n : ℕ} {k : ℕ → ℕ} :
 (Σ i : Fin n, Fin (k i)) ⊕ Fin (k n)→ (Σ i : Fin (Nat.succ n), Fin (k i)) :=
fun x =>
  match x with
  | Sum.inl ⟨i, x⟩ => ⟨⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self n)⟩, x⟩
  | Sum.inr x =>  ⟨⟨n, Nat.lt_succ_self n⟩, x⟩


#check Equiv.sigmaNatSucc

-- ⊕ adds additional element to Σ:
lemma sigmaNatSuccUltra {n : Nat} {k : ℕ → ℕ} :   (  Σ i : Fin (Nat.succ n) , Fin ( k i) )  ≃  (  Σ i : Fin n , Fin ( k i) ) ⊕ Fin (k n) :=
  {
    toFun := forward
    invFun := backward
    left_inv := by sorry
    right_inv := by sorry

  }


-- First step is to show, that ∑ i : Fin 4, Id  =  Fin 1 ⊕ Fin 2 ⊕ Fin 3
def sumIsSum {n : Nat} {k : Nat → Nat} :
   (  Σ i : Fin n , Fin ( k i) ) ≃ sumOfFin n k := by
    induction n with
    | zero =>
            simp
            reduce
            apply Equiv.equivOfIsEmpty

    | succ n ih =>
      -- convert to (***) ⊕ Fin(k n)
     -- apply Equiv.symm
      have reduced : sumOfFin (n + 1) k = (  (sumOfFin n k) ⊕ (Fin (k n)) ) := by
        rfl
      rw[reduced]
      #check Equiv.trans
      apply Equiv.trans
      apply sigmaNatSuccUltra
      apply sumCong
      exact ih



---------------------
-- STEP 2  - EQUALITY OF ⨁Fin and Fin+
---------------------

-- Show that  Fin k1 ⊕ Fin k2 ⊕ Fin k3 = Fin(k1 + k2 + k3)
def finSumnFinEquiv{n : Nat} {k : Nat → Nat} :
   sumOfFin n k  ≃ Fin (∑ i : Fin n, k i) := by
   induction n with
   | zero =>
             simp
             reduce
             apply Equiv.equivOfIsEmpty

   | succ n ih=>
      have reduced : sumOfFin (n + 1) k = (  (sumOfFin n k) ⊕ (Fin (k n)) ) := by
        rfl
      rw[reduced]
      apply Equiv.symm
      -- rewrite this into the form for finSumFinEquiv
      rw[ Fin.sum_univ_castSucc ]

      -- use finSumFinEquiv
      apply Equiv.trans
      apply Equiv.symm
      apply finSumFinEquiv

      apply Equiv.symm
      simp
      apply sumCong ih







--FINAL EQUALITY:

theorem finSigmanFinEquiv  {n : Nat} {k : Nat → Nat} :
 (  Σ i : Fin n , Fin ( k i) ) ≃  Fin (∑ i : Fin n, k i) := by
    apply Equiv.trans
    apply sumIsSum
    exact finSumnFinEquiv
