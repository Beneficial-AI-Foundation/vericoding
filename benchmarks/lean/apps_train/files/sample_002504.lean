=====Problem Statement=====
You are given a function f(X) = X^2. You are also given K lists. The ith list consists of N_i elements.

You have to pick one element from each list so that the value from the equation below is maximized:
S = (f(X_1) + f(X_2) + ... + f(X_k))%M
X_i denotes the element picked from the ith list. Find the maximized value S_max obtained.
% denotes the modulo operator.
Note that you need to take exactly one element from each list, not necessarily the largest element. You add the squares of the chosen elements and perform the modulo operation. The maximum value that you can obtain, will be the answer to the problem.

=====Input Format=====
The first line contains 2 space separated integers K and M.
The next K lines each contains an integer N_i, denoting the number of elements in the ith list, followed by space separated integers denoting the elements in the list. 

=====Constraints=====
1≤K≤7
1≤M≤1000
1≤N_i≤7
1≤Magnitude of elements in list≤10^9

=====Output Format=====
Output a single integer denoting the value S_max.

def List.product : List (List α) → List (List α)
  | [] => [[]]
  | (h :: t) => sorry

def sum [Add α] (l : List α) : α :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded
