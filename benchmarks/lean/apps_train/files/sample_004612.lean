When we have a 2x2 square matrix we may have up to 24 different ones changing the positions of the elements.

We show some of them
```
a  b   a  b    a  c    a  c   a  d    a  d    b  a    b  a
c  d   d  c    d  b    b  d   b  c    c  b    c  d    d  c
```
You may think to generate the remaining ones until completing the set of 24 matrices.

Given a certain matrix of numbers, that may be repeated or not, calculate the total number of possible matrices that may be generated, changing the position of the elements.

E.g:
Case one
```
A = [[1,2,3],
     [3,4,5]]   #a 2x3 rectangle matrix with number 3 twice
```     
generates a set of ```360``` different matrices

Case two
```
A = [[1,1,1], 
     [2,2,3], 
     [3,3,3]]
```
generates a set of ```1260``` different matrices.

Case three
```
A = [[1,2,3],
     [4,5,6],
     [7,8,9]]
```     
generates a set of ```362880``` different matrices

This kata is not meant to apply a brute force algorithm to try to count the total amount of marices.

Features of The Random Tests
``` 
number of tests = 100
2 ≤ m ≤ 9
2 ≤ n ≤ 9
``` 
Enjoy it!

Available only in Python 2, Javascript and Ruby by the moment.

def count_perms (matrix: List (List Nat)) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded
