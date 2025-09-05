In Chefland, types of ingredients are represented by integers and recipes are represented by sequences of ingredients that are used when cooking. One day, Chef found a recipe represented by a sequence $A_1, A_2, \ldots, A_N$ at his front door and he is wondering if this recipe was prepared by him.
Chef is a very picky person. He uses one ingredient jar for each type of ingredient and when he stops using a jar, he does not want to use it again later while preparing the same recipe, so ingredients of each type (which is used in his recipe) always appear as a contiguous subsequence. Chef is innovative, too, so he makes sure that in each of his recipes, the quantity of each ingredient (i.e. the number of occurrences of this type of ingredient) is unique ― distinct from the quantities of all other ingredients.
Determine whether Chef could have prepared the given recipe.

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first line of each test case contains a single integer $N$.
- The second line contains $N$ space-separated integers $A_1, A_2, \ldots, A_N$.

-----Output-----
For each test case, print a single line containing the string "YES" if the recipe could have been prepared by Chef or "NO" otherwise (without quotes).

-----Constraints-----
- $1 \le T \le 100$
- $1 \le N \le 10^3$
- $1 \le A_i \le 10^3$ for each valid $i$

-----Example Input-----
3
6
1 1 4 2 2 2
8
1 1 4 3 4 7 7 7
8
1 7 7 3 3 4 4 4

-----Example Output-----
YES
NO
NO

-----Explanation-----
Example case 1: For each ingredient type, its ingredient jar is used only once and the quantities of all ingredients are pairwise distinct. Hence, this recipe could have been prepared by Chef. 
Example case 2: The jar of ingredient $4$ is used twice in the recipe, so it was not prepared by Chef.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded