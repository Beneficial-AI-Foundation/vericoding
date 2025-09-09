/-
Chef just come up with a very good idea for his business. He needs to hire two group of software engineers. Each group of engineers will work on completely different things and people from different groups don't want to disturb (and even hear) each other. Chef has just rented a whole floor for his purposes in business center "Cooking Plaza". The floor is a rectangle with dimensions N over M meters. For simplicity of description the floor's structure, let's imagine that it is split into imaginary squares of size 1x1 called "cells".
The whole floor is split into rooms (not necessarily rectangular). There are some not noise-resistant walls between some of the cells. Two adjacent cells belong to the same room if they don't have the wall between them. Cells are considered adjacent if and only if they share an edge. Also, we say that relation "belong to the same room" is transitive. In other words we say that if cells A and B belong to the same room and B and C belong to the same room then A and C belong to the same room.
So we end up having a partition of the floor into rooms. It also means, that each point on the floor belongs to some room.
Chef have to distribute the rooms between engineers of two groups. Engineers from the different groups cannot seat in the same room. If engineers from a different groups seat in adjacent rooms, the walls these rooms share have to be noise-resistant. The cost of having one meter of wall isolated is K per month. Due to various reasons Chef has to pay an additional cost for support of each of the room (e.g. cleaning costs money as well). Interesting to know that support cost for a particular room may differ depending on engineers of which group seat in this room.
Chef doesn't know the number of people he needs in each group of engineers so he wants to minimize the money he needs to pay for all the floor rent and support. He will see how it goes and then redistribute the floor or find another floor to rent or whatever. Either way, you don't need to care about this.
Please pay attention to the restriction that all the rooms should be occupied by engineers of one of the teams. Also, it might happen that all the rooms will be assigned to the same team and this is completely okay.

-----Input-----
The first line of the input contains three integers N, M, W, K and R, where N and M denote size of the floor, W denote number of one-meter-length walls, K denote cost of having one-meter-length wall be noise-resistant and R denote the number of rooms in which floor is partitioned.
Next W lines contain four integers each X1, Y1, X2, Y2. This means that cells with coordinates X1, Y1 and X2, Y2 have a wall between them. It's guaranteed that this cells share an edge.
Next R lines will contain four space separated integers each X, Y, C1, C2. This should be treated as support cost per month in a room that contain cell X, Y is C1 for first group of engineers and C2 for second group of engineers. It's guaranteed that all of cells among these R cells belong to different rooms. All coordinates are indexed starting from 1.

-----Output-----
Output a single integer - sum of the rent and support costs per month.

-----Constraints-----
- 1 ≤ N, M ≤ 1000
- 1 ≤ W ≤ min(2*N*M, 150000)
- 1 ≤ X1 ≤ N
- 1 ≤ Y1 ≤ M
- 1 ≤ X2 ≤ N
- 1 ≤ Y2 ≤ M
- 1 ≤ K ≤ 10000
- 1 ≤ C1, C2 ≤ 10000
- Limitations on R is described in subtasks section.

-----Subtasks-----
- Subtask #1 [30 points]: 1 ≤ R ≤ 50
- Subtask #2 [70 points]: 1 ≤ R ≤ 500

-----Example-----
Input:
2 4 5 5 3
1 2 1 3
1 2 2 2
1 3 2 3
1 4 2 4
2 1 2 2
1 1 30 12
1 3 10 15
2 3 11 22
Output:
48

-----Explanation-----
Here's the scheme of the floor
The correct assignment is the following.

- The blue color denotes assignment to the first team. Total cost for renting two rooms for this team is 11 + 10 = 21.
- The red color denotes assignment to the second team. Total cost for renting the only room for the team is 12.
- There are 3 meters of walls between them, resulting in isolating cost of 15.
The grand total is 21 + 12 + 15 = 48
-/

-- <vc-helpers>
-- </vc-helpers>

def solve_engineer_groups (N M W K R : Nat) (walls : List (List Nat)) (rooms : List (List Nat)) : Nat :=
sorry

theorem solve_engineer_groups_basic (N M W K R : Nat) (walls rooms : List (List Nat)) :
  N = 2 ∧ M = 4 ∧ W = 5 ∧ K = 5 ∧ R = 3 ∧ 
  walls = [[1,2,1,3], [1,2,2,2], [1,3,2,3], [1,4,2,4], [2,1,2,2]] ∧
  rooms = [[1,1,30,12], [1,3,10,15], [2,3,11,22]] →
  solve_engineer_groups N M W K R walls rooms = 48 :=
sorry

theorem solve_engineer_groups_minimal (N M W K R : Nat) (walls rooms : List (List Nat)) :
  N = 1 ∧ M = 2 ∧ W = 1 ∧ K = 1 ∧ R = 1 ∧
  walls = [[1,1,1,2]] ∧
  rooms = [[1,1,1,1]] →
  solve_engineer_groups N M W K R walls rooms ≥ 0 :=
sorry

theorem solve_engineer_groups_no_walls (N M W K R : Nat) (walls rooms : List (List Nat)) :
  N = 2 ∧ M = 2 ∧ W = 0 ∧ K = 5 ∧ R = 1 ∧
  walls = [] ∧ 
  rooms = [[1,1,10,20]] →
  solve_engineer_groups N M W K R walls rooms = min 10 20 :=
sorry

theorem solve_engineer_groups_single_wall (N M W K R : Nat) (walls rooms : List (List Nat)) :
  N = 2 ∧ M = 2 ∧ W = 1 ∧ K = 5 ∧ R = 2 ∧
  walls = [[1,1,1,2]] ∧
  rooms = [[1,1,10,20], [1,2,15,25]] →
  solve_engineer_groups N M W K R walls rooms ≥ 0 :=
sorry

/-
info: 48
-/
-- #guard_msgs in
-- #eval solve_engineer_groups 2 4 5 5 3 [[1, 2, 1, 3], [1, 2, 2, 2], [1, 3, 2, 3], [1, 4, 2, 4], [2, 1, 2, 2]] [[1, 1, 30, 12], [1, 3, 10, 15], [2, 3, 11, 22]]

-- Apps difficulty: interview
-- Assurance level: guarded