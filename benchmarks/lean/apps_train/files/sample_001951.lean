You work in a big office. It is a 9 floor building with an elevator that can accommodate up to 4 people. It is your responsibility to manage this elevator.

Today you are late, so there are queues on some floors already. For each person you know the floor where he currently is and the floor he wants to reach. Also, you know the order in which people came to the elevator.

According to the company's rules, if an employee comes to the elevator earlier than another one, he has to enter the elevator earlier too (even if these employees stay on different floors). Note that the employees are allowed to leave the elevator in arbitrary order.

The elevator has two commands:   Go up or down one floor. The movement takes 1 second.  Open the doors on the current floor. During this operation all the employees who have reached their destination get out of the elevator. Then all the employees on the floor get in the elevator in the order they are queued up while it doesn't contradict the company's rules and there is enough space in the elevator. Each employee spends 1 second to get inside and outside the elevator. 

Initially the elevator is empty and is located on the floor 1.

You are interested what is the minimum possible time you need to spend to deliver all the employees to their destination. It is not necessary to return the elevator to the floor 1.

-----Input-----

The first line contains an integer n (1 ≤ n ≤ 2000) — the number of employees.

The i-th of the next n lines contains two integers a_{i} and b_{i} (1 ≤ a_{i}, b_{i} ≤ 9, a_{i} ≠ b_{i}) — the floor on which an employee initially is, and the floor he wants to reach.

The employees are given in the order they came to the elevator.

-----Output-----

Print a single integer — the minimal possible time in seconds.

-----Examples-----
Input
2
3 5
5 3

Output
10
Input
2
5 3
3 5

Output
12

-----Note-----

 Explaination for the first sample [Image] t = 0

[Image] t = 2

[Image] t = 3

[Image] t = 5

[Image] t = 6

[Image] t = 7

[Image] t = 9

[Image] t = 10

def List.maximum (l : List Nat) : Option Nat := 
  sorry 

def List.minimum (l : List Nat) : Option Nat := 
  sorry

def time_to_get_free (payload : List Nat) (floor : Nat) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: guarded