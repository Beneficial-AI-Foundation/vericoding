There was a big bank robbery in Tablecity. In order to catch the thief, the President called none other than Albert – Tablecity’s Chief of Police. Albert does not know where the thief is located, but he does know how he moves.

Tablecity can be represented as 1000 × 2 grid, where every cell represents one district. Each district has its own unique name “(X, Y)”, where X and Y are the coordinates of the district in the grid. The thief’s movement is as 

Every hour the thief will leave the district (X, Y) he is currently hiding in, and move to one of the districts: (X - 1, Y), (X + 1, Y), (X - 1, Y - 1), (X - 1, Y + 1), (X + 1, Y - 1), (X + 1, Y + 1) as long as it exists in Tablecity. 

Below is an example of thief’s possible movements if he is located in district (7,1):

[Image]

Albert has enough people so that every hour he can pick any two districts in Tablecity and fully investigate them, making sure that if the thief is located in one of them, he will get caught. Albert promised the President that the thief will be caught in no more than 2015 hours and needs your help in order to achieve that.

-----Input-----

There is no input for this problem. 

-----Output-----

The first line of output contains integer N – duration of police search in hours. Each of the following N lines contains exactly 4 integers X_{i}1, Y_{i}1, X_{i}2, Y_{i}2 separated by spaces, that represent 2 districts (X_{i}1, Y_{i}1), (X_{i}2, Y_{i}2) which got investigated during i-th hour. Output is given in chronological order (i-th line contains districts investigated during i-th hour) and should guarantee that the thief is caught in no more than 2015 hours, regardless of thief’s initial position and movement.  N ≤ 2015  1 ≤ X ≤ 1000  1 ≤ Y ≤ 2 

-----Examples-----
Input
В этой задаче нет примеров ввода-вывода.
This problem doesn't have sample input and output.
Output
Смотрите замечание ниже.
See the note below.

-----Note-----

Let's consider the following output:

2

5 1 50 2

8 1 80 2

This output is not guaranteed to catch the thief and is not correct. It is given to you only to show the expected output format. There exists a combination of an initial position and a movement strategy such that the police will not catch the thief.

Consider the following initial position and thief’s movement:

In the first hour, the thief is located in district (1,1). Police officers will search districts (5,1) and (50,2) and will not find him.

At the start of the second hour, the thief moves to district (2,2). Police officers will search districts (8,1) and (80,2) and will not find him.

Since there is no further investigation by the police, the thief escaped!

def Coordinates := (Nat × Nat × Nat × Nat)
def SearchPlan := (Nat × List Coordinates)

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded