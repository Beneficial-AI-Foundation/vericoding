Vasya and Kolya play a game with a string, using the following rules. Initially, Kolya creates a string s, consisting of small English letters, and uniformly at random chooses an integer k from a segment [0, len(s) - 1]. He tells Vasya this string s, and then shifts it k letters to the left, i. e. creates a new string t = s_{k} + 1s_{k} + 2... s_{n}s_1s_2... s_{k}. Vasya does not know the integer k nor the string t, but he wants to guess the integer k. To do this, he asks Kolya to tell him the first letter of the new string, and then, after he sees it, open one more letter on some position, which Vasya can choose.

Vasya understands, that he can't guarantee that he will win, but he wants to know the probability of winning, if he plays optimally. He wants you to compute this probability. 

Note that Vasya wants to know the value of k uniquely, it means, that if there are at least two cyclic shifts of s that fit the information Vasya knowns, Vasya loses. Of course, at any moment of the game Vasya wants to maximize the probability of his win.

-----Input-----

The only string contains the string s of length l (3 ≤ l ≤ 5000), consisting of small English letters only.

-----Output-----

Print the only number — the answer for the problem. You answer is considered correct, if its absolute or relative error does not exceed 10^{ - 6}.

Formally, let your answer be a, and the jury's answer be b. Your answer is considered correct if $\frac{|a - b|}{\operatorname{max}(1,|b|)} \leq 10^{-6}$

-----Examples-----
Input
technocup

Output
1.000000000000000

Input
tictictactac

Output
0.333333333333333

Input
bbaabaabbb

Output
0.100000000000000

-----Note-----

In the first example Vasya can always open the second letter after opening the first letter, and the cyclic shift is always determined uniquely.

In the second example if the first opened letter of t is "t" or "c", then Vasya can't guess the shift by opening only one other letter. On the other hand, if the first letter is "i" or "a", then he can open the fourth letter and determine the shift uniquely.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: unguarded
