import Mathlib
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Basic
open BigOperators
open Nat


-- 1.2: Formalize the concept of plane trees-----------------------------------------------------------------
inductive PlaneTree : Type
| branches : List PlaneTree  → PlaneTree

--In Lean, the absence of constructors implicitly represents the possibility of an empty tree. In this case,
--if no branches are provided, it implies that the tree is empty

-- But if we wanted better readability we could also add option "empty"
-- inductive PlaneTree : Type
-- | empty : PlaneTree
-- | branches : List PlaneTree → PlaneTree







-- 1.3: Formalize the concept of full binary trees.--------------------------------------------------------------

inductive FullBinaryTree : Type
| leaf : FullBinaryTree
| node : (T1 T2 : FullBinaryTree) → FullBinaryTree
deriving Repr

-- inductive FullBinaryTree : Type
-- | leaf : FullBinaryTree
-- | node : FullBinaryTree → FullBinaryTree → FullBinaryTree


-- TODO delete?
--neke zadeve z vaj, napisan da ne moti ker so spodaj neke zadeve z vaj
-- def full_binary_tree.height : full_binary_tree → ℕ
-- | .leaf => 0
-- | .join T1 T2 => max (T1.height) (T2.height) + 1




-- 1.4: Construct the type of full binary trees with n nodes, not counting the-----------------------------------
--leaves
inductive FullBinaryTreeWithNNodes : ℕ → Type
| empty : FullBinaryTreeWithNNodes 0 -- Represents an empty tree with 0 nodes
| node : Π {m n}, FullBinaryTreeWithNNodes m → FullBinaryTreeWithNNodes n → FullBinaryTreeWithNNodes (m + n + 1)
-- Constructor `node` represents a node in a full binary tree with m + n + 1 nodes.
-- It takes two subtrees of sizes m and n, respectively, and creates a new node.
