You are provided with the marks of entire class in Data structures exam out of 100. You need to calculate the number of students having backlog (passing marks is >=31) and the average of the class. But this average is not a normal average, for this average marks of students having backlog are not considered but they will be considered in number of students. Also print the index of topper’s marks and print the difference of everyone’s marks with respect to the topper. 
In first line print the number of students having backlog and average of the class. In second line print indices of all the toppers(in case of more than 1 topper print index of all toppers in reverse order). Next N lines print the difference of everyone’s marks with respect to topper(s).
Note- if all students have backlog than average will be 0.
INPUT
The first line of the input contains an integer T denoting the number of test cases.
Next line contains N denoting the no of students in the class.
The line contains N space seprated integers A1,A2,A3….AN denoting the marks of each student in exam.
OUTPUT
First line contains the number of students having backlog and the special average of marks as described above. Average must have 2 decimal places.
Next line contains the indices of all the toppers in given array in reverse order.
Next N lines contain the difference of every student’s marks with respect to toppers.
Constraints
1<= T <= 100
1<= N <= 30
0<= Ai<= 100
Example
Input
1
9
56 42 94 25 74 99 27 52 83
Output
2 55.55
5 
43
57
5
74
25
0
72
47
16

def sum (l: List Nat) : Nat :=
  l.foldl (· + ·) 0

def natToFloat (n : Nat) : Float :=
  Float.ofNat n

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded