import Mathlib
import Mathlib.Data.Nat.Choose.Basic

--TASK 6: Prove that Binomial(2n,n) is divisible by n+1

--Here we used the fact that catalan number C_n=binomial(2n,n)/(n+1)
--We know we should do task 7 before that to be able to use it, but if we say that
--this holds the proof is quite simple


-- Theorem: Binomial(2n, n) is divisible by n+1
theorem binom_2n_n_divisible_by_nsucc (n : ℕ) : (n + 1) ∣ Nat.centralBinom n := by
  -- We need to show that (n + 1) divides the central binomial coefficient, which is binomial(2n, n)

  -- Use the definition of the Catalan number: C_n = binomial(2n, n) / (n + 1)
  use catalan n

  -- Rewrite the central binomial coefficient in terms of the Catalan number
  rw [← succ_mul_catalan_eq_centralBinom n]

  -- The statement now shows that (n + 1) * catalan n = centralBinom n, which means (n + 1) divides centralBinom n

#check binom_2n_n_divisible_by_nsucc
