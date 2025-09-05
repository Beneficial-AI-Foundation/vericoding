Mohit(Ex GenSec ) is the most active member of the roasting club who loves giving tasks to other members. One day he observed that none of the members were paying attention to the online classes, so he decided to have some fun and overcome the boring lectures. He wrote N numbers on the virtual board (where the first number is 1, the last one is N and the ith number being i).
Then he asked M questions to every other member of the club. In each question, a number K was given by Mohit and the members had to give a single integer as an answer which will be the sum of all numbers present on the whiteboard.
There are some conditions that every member has to follow while answering.
- If K is already present on the whiteboard then swap the first and last number.
- Otherwise, replace the last number with K.

-----Input:-----
- First-line will consist of space-separated integers N and M. The board will contain the list of numbers from 1 to N and M is the number of questions that Mohit will ask.
- Next M lines contain the number Ki, which will be provided by Mohit and (1<=i<=M).

-----Output:-----
For each question, report the sum of all integers present

-----Constraints-----
- $1 \leq N,M \leq 1000000$
- $2 \leq K \leq 10^9$

-----Sample Input:-----
5 4
7
12 
10 
1  

-----Sample Output:-----
17
22  
20
20

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded