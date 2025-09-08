/-
Given the number n, return a string which shows the minimum number of moves to complete the tower of Hanoi consisting of n layers.
Tower of Hanoi : https://en.wikipedia.org/wiki/Tower_of_Hanoi

Example - 2 layered Tower of Hanoi 

Input: n=2

Start
[[2, 1], [], []]

Goal
[[], [], [2, 1]]

Expected Output : '[[2, 1], [], []]\n[[2], [1], []]\n[[], [1], [2]]\n[[], [], [2, 1]]'
-/

-- <vc-helpers>
-- </vc-helpers>

def hanoi_array (n : Nat) : String :=
  sorry

-- A valid tower has elements in strictly decreasing order

theorem tower_ordering {n : Nat} (tower : List Nat) : 
  tower.length ≥ 2 → ∀ i, i + 1 < tower.length → 
  tower.get! i > tower.get! (i+1) :=
  sorry

-- Each state has exactly 3 towers

theorem three_towers {n : Nat} (state : List (List Nat)) :
  state.length = 3 :=
  sorry

-- All numbers from 1 to n appear exactly once across all towers

theorem numbers_complete {n : Nat} (state : List (List Nat)) :
  (∀ x ∈ state.join, x ≤ n) ∧
  ∀ k, k ≤ n → k > 0 → k ∈ state.join :=
  sorry

-- There are exactly 2^n states in the solution

theorem states_count {n : Nat} (states : List (List (List Nat))) :
  states.length = 2^n :=
  sorry

-- Initial state has all discs on first pole

theorem initial_state {n : Nat} (states : List (List (List Nat))) :
  states.head!.get! 0 = List.range' n n ∧
  states.head!.get! 1 = [] ∧ 
  states.head!.get! 2 = [] :=
  sorry

-- Final state has all discs on last pole

theorem final_state {n : Nat} (states : List (List (List Nat))) :
  states.getLast!.get! 0 = [] ∧
  states.getLast!.get! 1 = [] ∧
  states.getLast!.get! 2 = List.range' n n :=
  sorry

-- Apps difficulty: introductory
-- Assurance level: guarded