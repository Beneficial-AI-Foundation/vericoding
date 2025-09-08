/-
A high school has a strange principal. On the first day, he has his students perform an odd opening day ceremony:

There are number of lockers "n" and number of students "n" in the school. The principal asks the first student to go to every locker and open it. Then he has the second student go to every second locker and close it. The third goes to every third locker and, if it is closed, he opens it, and if it is open, he closes it. The fourth student does this to every fourth locker, and so on. After the process is completed with the "n"th student, how many lockers are open?

The task is to write a function which gets any number as an input and returns the number of open lockers after last sudent complets his activity. So input of the function is just one number which shows number of lockers and number of students. For example if there are 1000 lockers and 1000 students in school then input is 1000 and function returns number of open lockers after 1000th student completes his action.

The given input is always an integer greater than or equal to zero that is why there is no need for validation.
-/

def sqrt (n : Nat) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def num_of_open_lockers (n : Nat) : Nat :=
  sorry

theorem num_open_lockers_is_floor_sqrt (n : Nat) :
  num_of_open_lockers n = sqrt n :=
sorry

theorem num_open_lockers_nonnegative (n : Nat) :
  num_of_open_lockers n ≥ 0 :=
sorry

theorem num_open_lockers_squared_bound (n : Nat) :
  (num_of_open_lockers n) * (num_of_open_lockers n) ≤ n :=
sorry

theorem num_open_lockers_next_squared_bound (n : Nat) :
  (num_of_open_lockers n + 1) * (num_of_open_lockers n + 1) > n :=
sorry

theorem num_open_lockers_zero :
  num_of_open_lockers 0 = 0 :=
sorry

theorem num_open_lockers_one : 
  num_of_open_lockers 1 = 1 :=
sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval num_of_open_lockers 0

/-
info: 2
-/
-- #guard_msgs in
-- #eval num_of_open_lockers 4

/-
info: 22
-/
-- #guard_msgs in
-- #eval num_of_open_lockers 500

-- Apps difficulty: introductory
-- Assurance level: unguarded