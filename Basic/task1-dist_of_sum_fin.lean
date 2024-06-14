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
--there is finSumFinEquiv, which proves n= 2
#check finSumFinEquiv
-- we coud use finSumFinEquiv to prove n=2, and than do induction from there
--Example:
-- ∑ i : Fin 4, Id  =  Fin 1 ⊕ Fin 2 ⊕ Fin 3 = Fin(1 + 2) ⊕ Fin 3 = Fin(1 + 2 + 3)

-- we need a connection between Σ and ⊕, that is
--A type representing Fin 1 ⊕ Fin 2 ⊕ Fin 3:

def sumOfFin : (n : Nat) → (k : Nat → Nat) → Type
  | 0, _ => PEmpty -- same as Fin 0
  | n + 1, k =>  (sumOfFin n (fun i => k (i))) ⊕ (Fin (k n))

def RsumOfFin : (n : Nat) → (k : Nat → Nat) → Type
  | 0, _ => PEmpty
  | n + 1, k => Sum (Fin (k 0)) (sumOfFin n (fun i => k (Fin.succ i)))

-- EXAMPLE USAGE:
def k_example : Fin 3 → Nat
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 2

#reduce sumOfFin 3 k_example  --

-- general example
def kId (n : Nat) (x : Fin n) : Nat := x
#reduce sumOfFin 10 (kId 10)
#reduce sumOfFin 0 (kId 0)


--  1. EQUALITY OF ⨁ AND Σ
-- First step is to show, that ∑ i : Fin 4, Id  =  Fin 1 ⊕ Fin 2 ⊕ Fin 3
def sumIsSum {n : Nat} {k : Nat → Nat} :
   (  Σ i : Fin n , Fin ( k i) ) ≃ sumOfFin n k := by
    induction n with
    | zero =>
            simp
            reduce
            apply Equiv.equivOfIsEmpty

    | succ n ih =>

    sorry



lemma sumCong (h: A ≃ B) : A ⊕ C ≃ B ⊕ C := by
  apply Equiv.sumCongr h
  apply Equiv.refl C


--2. EQUALITY OF ⨁Fin and Fin+
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
      exact sumCong ih





--FINAL EQUALITY:

theorem finSigmanFinEquiv  {n : Nat} {k : Nat → Nat} :
 (  Σ i : Fin n , Fin ( k i) ) ≃  Fin (∑ i : Fin n, k i) := by
    apply Equiv.trans
    apply sumIsSum
    exact finSumnFinEquiv


-- other stuf TODO DELETE!
def finSumnFinEquiv_cpy  {n : Nat} {k : Fin n → Nat} :
 (  Σ i : Fin n , Fin ( k i) ) ≃  Fin (∑ i : Fin n, k i) := by
  -- induction on lenght of k = k0, ..., k(n-1)
  induction n with
  -- if n = 0, everything is an empty type.
  | zero => --a few simplificationn + empty types are all equal
            ring_nf
            simp
            apply Equiv.equivOfIsEmpty


  -- n --> succ n
  | succ n ih =>

    apply Equiv.trans
    apply Equiv.sigmaCongr (β₂ := ?mot) ?base ?fiber
    case mot =>
      exact λ o => Fin (k (match o with | none => n | some i => Fin.castSucc i))
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


def finPiFinEquiv {m : ℕ} {n : Fin m → ℕ} : (∀ i : Fin m, Fin (n i)) ≃ Fin (∏ i : Fin m, n i) :=
  Equiv.ofRightInverseOfCardLE (le_of_eq <| by simp_rw [Fintype.card_pi, Fintype.card_fin])
    (fun f => ⟨∑ i, f i * ∏ j, n (Fin.castLE i.is_lt.le j), by
      induction' m with m ih
      · simp
      rw [Fin.prod_univ_castSucc, Fin.sum_univ_castSucc]
      suffices
        ∀ (n : Fin m → ℕ) (nn : ℕ) (f : ∀ i : Fin m, Fin (n i)) (fn : Fin nn),
          ((∑ i : Fin m, ↑(f i) * ∏ j : Fin i, n (Fin.castLE i.prop.le j)) + ↑fn * ∏ j, n j) <
            (∏ i : Fin m, n i) * nn by
        replace := this (Fin.init n) (n (Fin.last _)) (Fin.init f) (f (Fin.last _))
        rw [← Fin.snoc_init_self f]
        simp (config := { singlePass := true }) only [← Fin.snoc_init_self n]
        simp_rw [Fin.snoc_castSucc, Fin.snoc_last, Fin.snoc_init_self n]
        exact this
      intro n nn f fn
      cases nn
      · exact isEmptyElim fn
      refine (Nat.add_lt_add_of_lt_of_le (ih _) <| Nat.mul_le_mul_right _ (Fin.is_le _)).trans_eq ?_
      rw [← one_add_mul (_ : ℕ), mul_comm, add_comm]⟩)
    (fun a b => ⟨(a / ∏ j : Fin b, n (Fin.castLE b.is_lt.le j)) % n b, by
      cases m
      · exact b.elim0
      cases' h : n b with nb
      · rw [prod_eq_zero (Finset.mem_univ _) h] at a
        exact isEmptyElim a
      exact Nat.mod_lt _ nb.succ_pos⟩)
    (by
      intro a; revert a; dsimp only [Fin.val_mk]
      refine Fin.consInduction ?_ ?_ n
      · intro a
        haveI : Subsingleton (Fin (∏ i : Fin 0, i.elim0)) :=
          (finCongr <| prod_empty).subsingleton
        exact Subsingleton.elim _ _
      · intro n x xs ih a
        simp_rw [Fin.forall_iff, Fin.ext_iff] at ih
        ext
        simp_rw [Fin.sum_univ_succ, Fin.cons_succ]
        have := fun i : Fin n =>
          Fintype.prod_equiv (finCongr <| Fin.val_succ i)
            (fun j => (Fin.cons x xs : _ → ℕ) (Fin.castLE (Fin.is_lt _).le j))
            (fun j => (Fin.cons x xs : _ → ℕ) (Fin.castLE (Nat.succ_le_succ (Fin.is_lt _).le) j))
            fun j => rfl
        simp_rw [this]
        clear this
        dsimp only [Fin.val_zero]
        simp_rw [Fintype.prod_empty, Nat.div_one, mul_one, Fin.cons_zero, Fin.prod_univ_succ]
        change (_ + ∑ y : _, _ / (x * _) % _ * (x * _)) = _
        simp_rw [← Nat.div_div_eq_div_mul, mul_left_comm (_ % _ : ℕ), ← mul_sum]
        convert Nat.mod_add_div _ _
        -- Porting note: new
        refine (ih (a / x) (Nat.div_lt_of_lt_mul <| a.is_lt.trans_eq ?_))
        exact Fin.prod_univ_succ _
