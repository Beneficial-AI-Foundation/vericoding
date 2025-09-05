Mr. X stays in a mansion whose door opens in the North. He travels every morning to meet his friend Ms. Y walking a predefined path.

To cut the distance short, one day he decides to construct a skywalk from his place to his friend’s place. Help him to find the shortest distance between the two residences.

-----Input-----

The first line contains a single positive integer T <= 100, the number of test cases. T test cases follow. The only line of each test case contains a string which is the path from X to Y. The integer value represents the distance. The character R or L represents a Right or a Left respectively.

-----Output-----

For each test case, output a single line containing the minimum distance and the direction(N,S,W,E,NE,NW,SE,SW) of Y’s residence with respect to X’s residence. The output distance should have only 1 decimal place with no approximation. Print “0.0” if X’s and Y’s residence coincide.

-----Example-----
Input:
1
2 L 2 R 2 L 1

Output:
5.0NW

Explanation
Mr. X travels 2units and then takes a Left, and then he travels 2units and takes a Right, then after travelling 2units he takes a Left and finally travels 1unit to reach Y’s residence.
(Unlike Input, Output does not have spaces between the distance and direction)

def Point := Nat × Nat -- Position representation
def Direction := String -- Direction representation

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded