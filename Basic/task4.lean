import Mathlib.Logic.Equiv.Defs
import «Basic».trees

--TASK4: construct a bijection between list PlaneTree and PlaneTree

-- Define a function to convert a list of `PlaneTree`s to a `PlaneTree`
def listToPlaneTree : List PlaneTree → PlaneTree
  | l => PlaneTree.branches l
-- This function simply wraps the list into the `branches` constructor of `PlaneTree`

-- Define a function to convert a `PlaneTree` back to a list of `PlaneTree`s
def planeTreeToList : PlaneTree → List PlaneTree
  | PlaneTree.branches l => l
-- This function extracts the list from the `branches` constructor of `PlaneTree`

-- Prove that converting a list to a `PlaneTree` and back to a list yields the original list
theorem list_to_planeTree_to_list (l : List PlaneTree) :
  planeTreeToList (listToPlaneTree l) = l :=
rfl
-- This theorem is trivially true because the functions `listToPlaneTree` and `planeTreeToList`
-- are directly inverse operations. `listToPlaneTree l` creates `PlaneTree.branches l`,
-- and `planeTreeToList` then extracts the original list `l`.

-- Prove that converting a `PlaneTree` to a list and back to a `PlaneTree` yields the original tree
theorem planeTree_to_list_to_tree (t : PlaneTree) :
  listToPlaneTree (planeTreeToList t) = t :=
match t with
| PlaneTree.branches _ => rfl
-- This theorem is also trivially true because the functions `planeTreeToList` and `listToPlaneTree`
-- are directly inverse operations. `planeTreeToList t` extracts the list from `PlaneTree.branches`,
-- and `listToPlaneTree` then wraps that list back into `PlaneTree.branches`, resulting in the original tree `t`.

-- Define an equivalence between `List PlaneTree` and `PlaneTree`
def treeListEquiv : List PlaneTree ≃ PlaneTree := Equiv.mk
  listToPlaneTree          -- Function to convert from `List PlaneTree` to `PlaneTree`
  planeTreeToList          -- Function to convert from `PlaneTree` to `List PlaneTree`
  list_to_planeTree_to_list -- Proof that converting from `List PlaneTree` to `PlaneTree` and back to `List PlaneTree` yields the original list
  planeTree_to_list_to_tree -- Proof that converting from `PlaneTree` to `List PlaneTree` and back to `PlaneTree` yields the original tree

-- Check the type of `least_fixed_point_list_plane_tree` to confirm it is an equivalence
#check treeListEquiv
-- The type `least_fixed_point_list_plane_tree : List PlaneTree ≃ PlaneTree` confirms that we have
-- successfully defined a bijection (equivalence) between `List PlaneTree` and `PlaneTree`.
