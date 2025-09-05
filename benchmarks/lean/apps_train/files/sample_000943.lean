-----
HALLOWEEN EVE
-----

In some other world, today is Halloween Eve.There are N trees planted in Mr. Smith’s
garden. The height of the i-th tree (1≤i≤N) is h i meters.
He decides to choose K trees from these trees and decorate them with electric lights.
To make the scenery more beautiful, the heights of the decorated trees should be as
close to each other as possible.

More specifically, let the height of the tallest decorated tree be hmax meters, and the
height of the shortest decorated tree be hmin meters.
The smaller the value hmax−hmin is, the better. What is the minimum possible value of
hmax−hmin?

-----Constraints-----

	    2≤K< N ≤105 

1≤hi≤109

hi is an integer

-----Input Format-----

Input is given from Standard Input in the following format:

N K 

h1 

h2 

: 

hN

-----Output-----

Print the minimum possible value of hmax−hmin.

-----Example Text Case-----
Input:

5 3
10
15
11
14
12

Output:

2

Explanation

If we decorate the first, third and fifth trees, hmax=12,hmin=10 so hmax−hmin=2. This is
optimal.

def List.maximum (l : List Int) : Int :=
sorry

def List.minimum (l : List Int) : Int :=
sorry

def List.sort (l : List Int) : List Int :=
sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible
