Today, Chef decided to cook some delicious meals from the ingredients in his kitchen. There are $N$ ingredients, represented by strings $S_1, S_2, \ldots, S_N$. Chef took all the ingredients, put them into a cauldron and mixed them up.
In the cauldron, the letters of the strings representing the ingredients completely mixed, so each letter appears in the cauldron as many times as it appeared in all the strings in total; now, any number of times, Chef can take one letter out of the cauldron (if this letter appears in the cauldron multiple times, it can be taken out that many times) and use it in a meal. A complete meal is the string "codechef". Help Chef find the maximum number of complete meals he can make!

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first line of each test case contains a single integer $N$.
- $N$ lines follow. For each $i$ ($1 \le i \le N$), the $i$-th of these lines contains a single string $S_i$.

-----Output-----
For each test case, print a single line containing one integer — the maximum number of complete meals Chef can create.

-----Constraints-----
- $1 \le T \le 100$
- $1 \le N \le 100$
- $|S_1| + |S_2| + \ldots + |S_N| \le 1,000$
- each string contains only lowercase English letters

-----Example Input-----
3
6
cplusplus
oscar
deck
fee
hat
near
5
code
hacker
chef
chaby
dumbofe
5
codechef
chefcode
fehcedoc
cceeohfd
codechef

-----Example Output-----
1
2
5

-----Explanation-----
Example case 1: After mixing, the cauldron contains the letter 'c' 3 times, the letter 'e' 4 times, and each of the letters 'o', 'd', 'h' and 'f' once. Clearly, this is only enough for one "codechef" meal.
Example case 2: After mixing, the cauldron contains the letter 'c' 4 times, 'o' 2 times, 'd' 2 times, 'e' 4 times, 'h' 3 times and 'f' 2 times, which is enough to make 2 meals.

def max_meals (ingredients : List (List Char)) : Nat :=
  sorry

def count_char (c : Char) (s : List Char) : Nat :=
  (s.filter (fun x => x = c)).length

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded
