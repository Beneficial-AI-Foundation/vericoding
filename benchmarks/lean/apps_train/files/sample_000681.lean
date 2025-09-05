Now-a-days, Manish is becoming  famous for bank robbery in the country because of his cleverness, he never robs own his own.He has four workers A , B, C, and D , all working under him.All of the four take some amount for that. There are total N banks in the country and Manish wants to rob all the banks with minimum

amount spent on workers.Only one worker is allowed to rob the ith bank but following a condition that if one worker robs ith bank, then he can't rob (i+1) th bank.

So ,Manish wants you to calculate minimum amount that he has to spend on all workers to rob all N banks.

-----Input Format-----
First line consists number of test cases T.For each test case,

first line consists an integer N, number of banks in the country

and the next N line consists 4 integers amount taken by A,B,C and D respectively to rob ith bank.

-----Output format-----
For each test case ,output an integer, minimum amount paid  by Manish in separate line .

-----Constraint-----
- 1<=T<=1000
- 1<=N<=100000
- 1<=amount<=100000

-----Subtasks-----
Subtask-1 (10 points)
- 1<=T<=5
- 1<=N<=10
- 1<=amount<=10
Subtask-1 (30 points)
- 1<=T<=100
- 1<=N<=1000
- 1<=amount<=1000
Subtask-1 (60 points)
Original Constraints 
Sample Input
1
3
4 7 2 9
5 6 4 7
2 6 4 3

Sample Output
10

def minRobberyCost (n : Nat) (costs : List (List Nat)) : Nat :=
  sorry

def listMin (xs : List Nat) : Nat :=
  match xs with
  | [] => 0
  | h :: t => List.foldl min h t

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded