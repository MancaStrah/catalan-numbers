import «Basic».catalan
import «Basic».trees
import «Basic».ballot
import Mathlib
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Basic
open BigOperators
open Nat


--TODO - posodobi arhitekturo tako, da bodo v Basic.lean samo klici na implementacije


-- SMALL TASKS:
--Here are the solutions for small tasks.
--Implementations are in seperate folders.

-- Small task 1: Recursive definition of catalan numbers
#check catalan_number
#eval catalan 0
#eval catalan 1
#eval catalan 2
#eval catalan 3
#eval catalan 7

-- Small task 2: Plane trees
#check PlaneTree

-- Small task 3: Full binary trees
#check full_binary_tree
def tree13 := full_binary_tree.join full_binary_tree.leaf full_binary_tree.leaf

#eval tree13

-- Small task 4: Full binary trees with n nodes
#check FullBinaryTreeWithNNodes


-- Small task 5: Ballot sequences of lenght n
#check ballot




-- LARGER TASKS -TODO

-- 2.1: Construct a bijection ...



-- 2.2: Construct a bijection ....




-- 2.7
-- The binomial coefficient (choose function)
def binomial (n k : ℕ) : ℕ := Nat.choose n k

--Proving the catalan formula for base case where n=0
theorem catalan_number_formula_base : catalan_number 0 = (binomial (2 * 0) 0) / (0 + 1) := by
  rw [catalan_number]
  have h : binomial 0 0 = 1 := Nat.choose_zero_right 0
  rw [h, Nat.zero_add, Nat.div_one]









-- STARE STVARI IZ VAJ
--TODO delete?




/-- Binary trees -/
inductive binary_tree : Type
| root
| succ: binary_tree → binary_tree
| join: (T1 T2 : binary_tree) → binary_tree

/-- The height of a binary tree -/
def binary_tree.height : binary_tree → ℕ
| .root => 0
| .succ T => T.height + 1
| .join T1 T2 => max T1.height T2.height + 1

/-- The number of leaves of a binary tree -/
def binary_tree.number_of_leaves : binary_tree → ℕ
| .root => 1
| .succ T => T.number_of_leaves
| .join T1 T2 => T1.number_of_leaves + T2.number_of_leaves



/-- Converting a full binary tree into a binary tree-/
def binary_tree_of_full_binary_tree : full_binary_tree → binary_tree
| .leaf => .root
| .join T1 T2 => .join (binary_tree_of_full_binary_tree T1) (binary_tree_of_full_binary_tree T2)

/-- Converting a binary tree into a full binary tree, by forgetting its unary branchings-/
def full_binary_tree_of_binary_tree : binary_tree → full_binary_tree
| .root => .leaf
| .succ T => full_binary_tree_of_binary_tree T
| .join T1 T2 => .join (full_binary_tree_of_binary_tree T1) (full_binary_tree_of_binary_tree T2)


theorem eq_height_binary_tree_of_full_binary_tree : (T : full_binary_tree) → T.height = (binary_tree_of_full_binary_tree T).height := by
intro T
induction' T with _ _ T1_H T2_H
rfl
simp [full_binary_tree.height]
simp [binary_tree.height]
rw [T1_H, T2_H]


def full_binary_tree.number_of_leaves : full_binary_tree → ℕ
| .leaf => 1
| .join T1 T2 => T1.number_of_leaves + T2.number_of_leaves


-- theorem eq_number_of_leaves_binary_tree_of_full_binary_tree : (T : full_binary_tree) → T.number_of_leaves =
-- (binary_tree_of_full_binary_tree T).number_of_leaves := by
-- sorry


/-- The type of binary trees with n nodes -/
inductive binary_tree_with_nodes: ℕ → Type
| root : binary_tree_with_nodes 1
| succ : {n : ℕ} → binary_tree_with_nodes n → binary_tree_with_nodes (n + 1)
| join: {n m : ℕ} → binary_tree_with_nodes n → binary_tree_with_nodes m → binary_tree_with_nodes (n + m + 1)


def binary_tree_of_binary_tree_with_nodes (n : ℕ): binary_tree_with_nodes n → binary_tree
| .root => .root
| .succ T => .succ (binary_tree_of_binary_tree_with_nodes _ T)
| .join T1 T2 => .join  (binary_tree_of_binary_tree_with_nodes _ T1)  (binary_tree_of_binary_tree_with_nodes _ T2)



-- Vaje 2: 12. 4. 2024


inductive plane_tree: Type
| make_plane_tree : (n: ℕ) → (Fin n → plane_tree) → plane_tree




-- Vaje 3: 19. 4. 2024
