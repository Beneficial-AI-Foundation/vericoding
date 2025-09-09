/-
=====Function Descriptions=====
We have seen the applications of union, intersection, difference and symmetric difference operations, but these operations do not make any changes or mutations to the set.

We can use the following operations to create mutations to a set:

.update() or |=
Update the set by adding elements from an iterable/another set.

>>> H = set("Hacker")
>>> R = set("Rank")
>>> H.update(R)
>>> print H
set(['a', 'c', 'e', 'H', 'k', 'n', 'r', 'R'])

.intersection_update() or &=
Update the set by keeping only the elements found in it and an iterable/another set.

>>> H = set("Hacker")
>>> R = set("Rank")
>>> H.intersection_update(R)
>>> print H
set(['a', 'k'])

.difference_update() or -=
Update the set by removing elements found in an iterable/another set.

>>> H = set("Hacker")
>>> R = set("Rank")
>>> H.difference_update(R)
>>> print H
set(['c', 'e', 'H', 'r'])

.symmetric_difference_update() or ^=
Update the set by only keeping the elements found in either set, but not in both.

>>> H = set("Hacker")
>>> R = set("Rank")
>>> H.symmetric_difference_update(R)
>>> print H
set(['c', 'e', 'H', 'n', 'r', 'R'])

=====Problem Statement=====
You are given a set A and N number of other sets. These N number of sets have to perform some specific mutation operations on set A.

Your task is to execute those operations and print the sum of elements from set A.

=====Input Format=====
The first line contains the number of elements in set A.
The second line contains the space separated list of elements in set A.
The third line contains integer N, the number of other sets.
The next 2 * N lines are divided into N parts containing two lines each.
The first line of each part contains the space separated entries of the operation name and the length of the other set.
The second line of each part contains space separated list of elements in the other set.

=====Constraints=====
0<len(set(A))<1000
0<len(otherSets)<100
0<N<100

=====Output Format=====
Output the sum of elements in set A.
-/

def Operation := String
def OperationList := List (Operation × List Nat)

-- <vc-helpers>
-- </vc-helpers>

def process_set_operations (initial : List Nat) (operations : OperationList) : Nat :=
  sorry

theorem process_set_operations_result {initial : List Nat} {ops : OperationList} :
  ∃ (n : Nat), process_set_operations initial ops = n :=
  sorry

theorem process_set_operations_nonnegative {initial : List Nat} {ops : OperationList} :
  process_set_operations initial ops ≥ 0 :=
  sorry

theorem process_set_operations_empty :
  process_set_operations [] [] = 0 :=
  sorry

theorem update_operations_monotonic {initial : List Nat} :
  process_set_operations initial [] ≤ process_set_operations initial [("update", [0,1,2,3,4])] :=
  sorry

theorem intersection_with_self {initial : List Nat} :
  process_set_operations initial [] = process_set_operations initial [("intersection_update", initial)] :=
  sorry

-- Apps difficulty: introductory
-- Assurance level: guarded