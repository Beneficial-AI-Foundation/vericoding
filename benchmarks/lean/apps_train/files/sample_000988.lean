The snakes want to build a temple for Lord Cobra. There are multiple strips of land that they are looking at, but not all of them are suitable. They need the strip of land to resemble a coiled Cobra. You need to find out which strips do so.
Formally, every strip of land, has a length. Suppose the length of the i-th strip is is Ni, then there will be Ni integers, Hi1, Hi2, .. HiNi, which represent the heights of the ground at various parts of the strip, in sequential order. That is, the strip has been divided into Ni parts and the height of each part is given. This strip is valid, if and only if all these conditions are satisfied:
- There should be an unique 'centre' part. This is where the actual temple will be built. By centre, we mean that there should be an equal number of parts to the left of this part, and to the right of this part.
- Hi1 = 1
- The heights keep increasing by exactly 1, as you move from the leftmost part, to the centre part.
- The heights should keep decreasing by exactly 1, as you move from the centre part to the rightmost part. Note that this means that HiNi should also be 1.
Your job is to look at every strip and find if it's valid or not.

-----Input-----
- The first line contains a single integer, S, which is the number of strips you need to look at. The description of each of the S strips follows
- The first line of the i-th strip's description will contain a single integer: Ni, which is the length and number of parts into which it has been divided.
- The next line contains Ni integers: Hi1, Hi2, .., HiNi. These represent the heights of the various parts in the i-th strip.

-----Output-----
- For each strip, in a new line, output "yes" if is a valid strip, and "no", if it isn't.

-----Constraints-----
- 1 ≤ S ≤ 100 
- 3 ≤ Ni ≤ 100 
- 1 ≤ Hij ≤ 100 

-----Example-----
Input:
7
5
1 2 3 2 1
7
2 3 4 5 4 3 2
5
1 2 3 4 3
5
1 3 5 3 1
7
1 2 3 4 3 2 1
4
1 2 3 2
4
1 2 2 1

Output:
yes
no
no
no
yes
no
no

-----Explanation-----
In the first strip, all the conditions are satisfied, hence it is valid.
In the second strip, it does not start with a 1, and hence is invalid.
In the third strip, it keeps increasing even past the centre, instead of decreasing. Hence invalid.
The fourth strip does not increase and decrease by exactly 1. Hence invalid.
The fifth satisfies all conditions and hence is valid.
The sixth and seventh strip do not have a 'centre' part. Because for every part, there are either more parts to its right than its left, or more parts on its left than its right. Hence both the strips are invalid.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
