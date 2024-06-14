import «Basic».catalan
import «Basic».trees
import «Basic».ballot
import Mathlib
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Basic
import «Basic».task1
import «Basic».task4
import «Basic».task5
import «Basic».task6

open BigOperators
open Nat


------------------
-- SMALL TASKS:
------------------
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
#check ballot_sequnces_n



----------------------
-- LARGER TASKS
----------------------
