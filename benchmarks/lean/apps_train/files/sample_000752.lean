Sultan, the freestyle wrestler, you all know him. He broke multiple records in the history of all wrestling leagues. Now 20 years have passed, Sultan has grown old. He has two sons, he wants them to be like him. Sultan being orthodox goes to his astrologer, where he is told that his sons shall be invincible like him. 
Sultan starts to train them. After training, his son Multan & Fultan, having strengths are M and F respectively, decide to fight. They can defeat if the strength of challengers Si is a positive integer multiple of their strength else they lose. Multan fights first, then Fultan. A challenger once knocked out cannot challenge them again. Sultan's sons are still not very good wrestlers. Sultan considers them wrestlers if they both combined are able to win at least 70% of the all the fights. Also, he wants to know who is a better wrestler of the two. Your task is to help Sultan in this venture. Print "Yes" (without quotes) if they are able to win, else print "No" (without quotes). If yes, also name whether, "Multan" or "Fultan" is a better wrestler, if both win equally print “Both”.

-----Input-----
- First line contains single integer T denoting test cases.
- Second Line contains single integer N for number of challengers.
- Third Line contains space separated two integer denoting strength M & F
- Next Line contains strength space separated N integer ith of which denoting Si of N challengers respectively.

-----Output-----
- Yes or No corresponding the result.
- Also, if Yes, print, Multan, Fultan, Both accordingly. 

-----Constraints-----
- 1 ≤ T ≤ 100
- 1 ≤ N ≤ 1000
- 1 ≤ M, F ≤ 109
- 0 ≤ Si ≤ 109

-----Example-----
Input:
2
7
2 3
4 5 7 8 9 10 14
6
5 7
1 2 8 9 10 11

Output:
Yes
Multan
No

-----Explanation-----
Example case 1.

Multan (M) defeats total 4 challengers with strengths 4, 8, 10, 14 and Fultan (F) defeats 1 challenger with strength 9. Their total wins are 5 out of 7 and win accuracy of 71.4%. Hence, 'Yes' and since Multan is better wrestler so 'Multan'

Example case 2.
Multan defeats 1 and Fultan defeat 0 challengers. Total wins 1 out of 6 with accuracy 16.67% Hence, No.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded