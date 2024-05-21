import Mathlib


-- 1: Formalization tasks

-- 1.1: Formalize the crecursive definition of the catalan numbers.
def catalan_number : Nat → Nat
| 0 => 1
| succ n => ∑ i : Fin (succ n), (catalan_number i) * (catalan_number (n - i))


#eval catalan 0
#eval catalan 1
#eval catalan 2
#eval catalan 3




-- 1.2: Formalize the concept of plane trees






-- 1.3: Formalize the concept of full binary trees.

inductive full_binary_tree : Type
| root
| join : (T1 T2 : full_binary_tree) → full_binary_tree

def full_binary_tree.height : full_binary_tree → ℕ
| .root => 0
| .join T1 T2 => max (T1.height) (T2.height) + 1






-- 1.4: Construct the type of full binary trees with n nodes, not counting the
leaves



-- 1.5: Define the type of ballot sequences of length n





-- LARGER TASKS

-- 2.1: Construct a bijection ...


-- 2.2: Construct a bijection ....












-- STARE STVARI IZ VAJ




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
| .root => .root
| .join T1 T2 => .join (binary_tree_of_full_binary_tree T1) (binary_tree_of_full_binary_tree T2)

/-- Converting a binary tree into a full binary tree, by forgetting its unary branchings-/
def full_binary_tree_of_binary_tree : binary_tree → full_binary_tree
| .root => .root
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
| .root => 1
| .join T1 T2 => T1.number_of_leaves + T2.number_of_leaves


theorem eq_number_of_leaves_binary_tree_of_full_binary_tree : (T : full_binary_tree) → T.number_of_leaves =
(binary_tree_of_full_binary_tree T).number_of_leaves := by
sorry


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
