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


--def sigmaNatSucc1 (f : ℕ → Type u) : (Σ n, f n) ≃ Sum (f 0) (Σ n, f (n + 1)) :=
def sigmaNatSuccUltra {n : Nat} {k : ℕ → ℕ } (f : ℕ → Type u) :
(  Σ i : Fin (Nat.succ n) , Fin ( k i) )  ≃  (  Σ i : Fin n , Fin ( k i) ) ⊕ Fin (k n) :=
  ⟨fun x =>
   --@Sigma.casesOn ℕ f (fun _ => Sum (f 0) (Σn, f (n + 1))) x fun n =>
    @Sigma.casesOn ℕ (fun m => Fin m)  (fun _ =>((  Σ i : Fin n , Fin ( k i) ) ⊕ Fin (k n)) )x fun n =>
      @Nat.casesOn (fun i => f i → Sum (f 0) (Σn : ℕ, f (n + 1))) n (fun x : f 0 => Sum.inl x)
        fun (n : ℕ) (x : f n.succ) => Sum.inr ⟨n, x⟩,
    Sum.elim (Sigma.mk 0) (Sigma.map Nat.succ fun _ => id), by rintro ⟨n | n, x⟩ <;> rfl, by
    rintro (x | ⟨n, x⟩) <;> rfl⟩



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
