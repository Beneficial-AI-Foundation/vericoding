-----Problem-----

			Nikki's latest work is writing a story of letters. However, she finds writing story so boring that, after working for three hours, she realized that all she has written are M long words consisting entirely of letters A and B. Having accepted that she will never finish the story in time, Nikki has decided to at least have some fun with it by counting bubbly words.

			Now Nikki is connecting pairs of identical letters (A with A, B with B) by drawing lines above the word. A given word is bubbly if each letter can be connected to exactly one other letter in such a way that no two lines intersect. So here is your task. Help Nikki count how many words are bubbly.

-----Input-----
- 
			The first line of input contains the positive integer M, the number of words written down by Nikki.

- 
			Each of the following M lines contains a single word consisting of letters A and B, with length

			between 2 and 10^5, inclusive. The sum of lengths of all words doesn't exceed 10^6.

-----Output-----

			The first and only line of output must contain the number of bubbly words.

-----Constraints-----
- 
			1 ≤ M ≤ 100

-----Sample Input-----

3

ABAB

AABB

ABBA

-----Sample Output-----
2

-----Explanation-----
- 
					 ABAB - It is not bubbly as A(indexed 1) will connect to A(indexed 3) by a line and when we try to connect B(indexed 2) with B(indexed 4) by a line then it will intersect with the line b/w A and A.

- 
					AABB - It is bubbly as line b/w A and A will not intersect with the line b/w B and B.

- 
ABBA -It is also bubbly as lines will not intersect. We can draw line b/w A and A above the line b/w B and B.
				 p { text-align:justify }

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded
