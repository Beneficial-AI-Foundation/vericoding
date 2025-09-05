It's John's birthday; he has brought some candies in distribute among N of his friends. Being a good friend, he decided to distribute all of his candies equally among his friend and he don't want to keep any for himself. He left the task of distributing candies up to his friends, but his friends haven't done a great job in distributing them and now they all have unequal amount of candies.
He asked all of his friends to keep all the candies in their hands (A[1] to A[N]) so that he can redistribute the candies. Taking a candy away from someone makes them sad and makes the person who gets it happy. Thus, you do not want to do many operations on the number of candies.
Here each operation stands for, taking away 1 candy from someone and giving it to somebody else.
After applying the operations, he might not be able to distribute all the candies among all of your friends, and you might need to buy some more candies as well. Buying each candy will be counted as 1 operation as well. John is saving up for his birthday party in the evening and so he wants to spend the least amount of money on candies as possible.
Thus, he asks for your help. You have to find the minimum number of operations required to make the distributions equal.

-----Input:-----
- The first line consists of the number T representing the number of test cases.
- Each test case consists of 2 lines.
- The first line contains of the number N representing the number of friends.
- The second line contains space separated numbers (A[1] to A[N]) representing the number of candies each friend currently has.

-----Output:-----
For each test case, you much print the minimum number of operations.

-----Constraints-----
- $1 \leq T \leq 10$
- $1 \leq N \leq 10^5$
- $0 \leq A[i] \leq 10^9$

-----Sample Input:-----
3

4

7 8 6 4

6

7 3 10 2 3 8

1

10   

-----Sample Output:-----
4

10

0

def List.sum : List Nat → Nat
  | [] => 0
  | x::xs => x + sum xs

inductive Perm {α : Type} : List α → List α → Prop where
  | nil : Perm [] []
  | cons : ∀ (x : α) (l₁ l₂ : List α), Perm l₁ l₂ → Perm (x::l₁) (x::l₂)
  | swap : ∀ (x y : α) (l : List α), Perm (x::y::l) (y::x::l)
  | trans : ∀ {l₁ l₂ l₃ : List α}, Perm l₁ l₂ → Perm l₂ l₃ → Perm l₁ l₃

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible
