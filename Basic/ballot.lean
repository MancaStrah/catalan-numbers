import Mathlib.Tactic

/- small task 5 -/
/- ballot sequences -/

-- A ballot sequence is a sequence of votes in which the number of votes for one candidate (say A)
-- is never less than the number of votes for another candidate (say B) at any point in the sequence.
-- More formally, for any prefix of the sequence, the number of votes for candidate A must be at least
-- the number of votes for candidate B.

-- The definition below captures this concept for unbalanced ballot sequences.
-- Here, 1 represents a vote for candidate A and -1 represents a vote for candidate B.

def ballot_sequnces_n (n : ℕ) : Set (List ℤ) :=
  {
    -- The set of lists l such that:
    l |
      ∃ p : ℕ, ∃ q : ℕ,
      -- There exist natural numbers p and q such that p + q = n
      p + q = n ∧
      -- The list l contains exactly p occurrences of 1 and q occurrences of -1
      l.count 1 = p ∧ l.count (-1) = q ∧
      -- Each element x in the list l must be either 1 or -1
      ∀ x ∈ l, (x = (1 : ℤ) ∨ x = -1) ∧
      -- For every prefix of length i (where i ranges from 0 to n),
      -- the sum of the elements in the prefix must be non-negative.
      --This way we are sure that A (1) always has as least as many votes as B (-1)
      ∀ i ≤ n, List.sum (List.take i l) ≥ 0
  }
