Sherlock Holmes has decided to start a new academy to some of the young lads. He has conducted several tests and finally selected N equally brilliant

students.Now he don't know whether to train all the N students or not. Now since Holmes was in a confusion, Watson came up with an idea. He wanted to

test the obedience of the students. So during the camp, the students were given some Swiss Chocolates as gifts each time when they passed a level.Now some of them have

finished eating all the chocolates, some of them had some remaining. Now to test their team chemistry and IQ skills, Watson told the lads to arrange themselves in such 
a way that,  number of chocolates of the ith kid should be equal to the sum of   (i-1)th kid and (i-2)th kid. Now they have arranged themselves in an order.
Now Sherlock announced that he will select the students who have formed the line according to this order. But since there can be many such small groups among the

entire N kids, he will select a sequence of kids such that the length of the sequence is maximized, meanwhile satisfying the above condition 

-----Input-----
First line is an integer T which denotes the total number of test cases. Each of the next T lines contains an integer N which denotes, N students. The next 
line contains N spaced integers.where it denotes the order in which the kids arranged themselves. 

-----Output-----
Each line contains an integer which denotes the maximum number of students among the N students who have arranged themselves according the rule said by Watson.It is guaranteed that Holmes will select atleast 1 or 2 students

-----Constraints-----
- 1 ≤ T ≤ 10
- 1 ≤ N ≤ 10^5
- 1 ≤ Each of next N integers ≤ 10^9

-----Subtasks-----
Subtask #1 : (20 points)
- 1 ≤ T ≤ 10
- 1 ≤ N≤ 100
- 1 ≤ Each element≤ 10^3

Subtask 2 : (80 points) 

- 1 ≤ T ≤ 10
- 1 ≤ N≤ 100000
- 1 ≤ Each element≤ 10^9

-----Example-----
Input:
2
5
2 3 5 1 2
3
1 2 3

Output:
3
3

-----Explanation-----
Example case 1. Here the first kid has 2 chocolates, second has 3 chocolates, third kid has 5 chocolates, which is the sum of first kid's total chocolates 
and second kid's chocolate. Forth student has only 1 chocolate where he did not follow the rule. So the maximum number of kids who arranged themselves in the order was 
3. That is students at index 1 to index 3.

def find_max_sequence_length (n : Nat) (arr : List Int) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible
