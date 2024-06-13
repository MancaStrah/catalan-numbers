import Mathlib.Logic.Equiv.Defs
import «Basic».trees

--TASK 5:Construct the rotating isomorphism, which is the isomorphism between
--plane trees and full binary trees.


-- Define a leaf for PlaneTree as an empty list of branches
@[inline]
def PlaneTree.leaf : PlaneTree := PlaneTree.branches []

-- Define a join function to combine a PlaneTree with another list of PlaneTrees
@[simp]
def PlaneTree.join : PlaneTree → PlaneTree → PlaneTree
| left, PlaneTree.branches rights => PlaneTree.branches (List.cons left rights)


-- Convert FullBinaryTree to PlaneTree
def full_binary_tree_to_plane_tree : FullBinaryTree → PlaneTree
| FullBinaryTree.leaf => PlaneTree.leaf
| FullBinaryTree.node T1 T2 => PlaneTree.join (full_binary_tree_to_plane_tree T1) (full_binary_tree_to_plane_tree T2)

-- Theorem proving that converting a FullBinaryTree.leaf to PlaneTree yields PlaneTree.leaf
theorem bt_leaf_to_pt_leaf : full_binary_tree_to_plane_tree FullBinaryTree.leaf = PlaneTree.leaf := rfl

-- Theorem proving that converting a FullBinaryTree.node to PlaneTree correctly joins the subtrees
theorem bt_node_to_pt_node (left : FullBinaryTree) (right : FullBinaryTree) :
  full_binary_tree_to_plane_tree (FullBinaryTree.node left right) =
  PlaneTree.join (full_binary_tree_to_plane_tree left) (full_binary_tree_to_plane_tree right) := rfl

#check bt_leaf_to_pt_leaf
#check bt_node_to_pt_node

-- Convert PlaneTree to FullBinaryTree
def plane_tree_to_full_binary_tree : PlaneTree → FullBinaryTree
| PlaneTree.branches [] => FullBinaryTree.leaf
| PlaneTree.branches (left :: rights) => FullBinaryTree.node (plane_tree_to_full_binary_tree left) (plane_tree_to_full_binary_tree (PlaneTree.branches rights))

-- Theorem proving that converting PlaneTree.leaf to FullBinaryTree yields FullBinaryTree.leaf
theorem pt_leaf_to_bt_leaf : plane_tree_to_full_binary_tree PlaneTree.leaf = FullBinaryTree.leaf := rfl

-- Theorem proving that converting a non-empty PlaneTree.branches to FullBinaryTree correctly creates a node
theorem pt_branches_to_bt_node (left : PlaneTree) (rights : List PlaneTree) :
  plane_tree_to_full_binary_tree (PlaneTree.branches (left :: rights)) =
  FullBinaryTree.node (plane_tree_to_full_binary_tree left) (plane_tree_to_full_binary_tree (PlaneTree.branches rights)) := by
  dsimp [plane_tree_to_full_binary_tree]
  rw [WellFounded.fix_eq]


#check pt_leaf_to_bt_leaf
#check pt_branches_to_bt_node

-- Define the rotating isomorphism between FullBinaryTree and PlaneTree
def rotating_isomorphism : FullBinaryTree ≃ PlaneTree :=
{
  toFun := full_binary_tree_to_plane_tree, -- Function to convert FullBinaryTree to PlaneTree
  invFun := plane_tree_to_full_binary_tree, -- Function to convert PlaneTree to FullBinaryTree

  -- Proof that converting to PlaneTree and back to FullBinaryTree yields the original tree
  left_inv := by
    -- Introduce the FullBinaryTree 'f' to work with
    intro f

    -- Perform induction on the structure of 'f'
    induction f with
    | leaf =>
      -- Base case: If 'f' is a leaf, directly apply the theorem for leaf
      apply pt_leaf_to_bt_leaf
    | node T1 T2 H1 H2 =>
      -- Inductive step: If 'f' is a node, with left subtree T1 and right subtree T2
      -- Rewrite the goal using the node conversion theorem
      rw [bt_node_to_pt_node]

      -- Case analysis on the result of converting the right subtree T2
      cases e : full_binary_tree_to_plane_tree T2

      -- Simplify the goal
      simp

      -- Rewrite the goal with the results of the induction hypotheses H1 and H2
      rw [pt_branches_to_bt_node, H1, ← e, H2],

  -- Proof that converting to FullBinaryTree and back to PlaneTree yields the original tree
  right_inv :=
    -- Use the recursor for PlaneTree to perform structural induction
    (@PlaneTree.rec
      -- Main goal: For any PlaneTree 'p', converting to FullBinaryTree and back should yield 'p'
      (λ p => full_binary_tree_to_plane_tree (plane_tree_to_full_binary_tree p) = p)

      -- Goal for the 'branches' constructor: If 'p' is 'PlaneTree.branches branches', converting should yield 'PlaneTree.branches branches'
      (λ branches => full_binary_tree_to_plane_tree (plane_tree_to_full_binary_tree (PlaneTree.branches branches)) = PlaneTree.branches branches)

      -- Induction step: Use the induction hypothesis
      (λ branches H => H)

      -- Base case: If 'p' is a leaf, converting should yield 'PlaneTree.leaf'
      (bt_leaf_to_pt_leaf)

      -- Induction case: If 'p' is 'PlaneTree.branches (left :: rights)', show conversion correctness
      (λ left rights HL HR => by
        -- Unfold the definition of the conversion function
        unfold plane_tree_to_full_binary_tree

        -- Simplify the goal
        simp

        -- Rewrite the goal using the node conversion theorem and induction hypotheses
        rw [bt_node_to_pt_node, HL, HR]

        -- Complete the proof with reflexivity
        rfl))
}

#check rotating_isomorphism
