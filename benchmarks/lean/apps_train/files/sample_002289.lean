/-
The round carousel consists of $n$ figures of animals. Figures are numbered from $1$ to $n$ in order of the carousel moving. Thus, after the $n$-th figure the figure with the number $1$ follows. Each figure has its own type — the type of the animal corresponding to this figure (the horse, the tiger and so on). The type of animal of the $i$-th figure equals $t_i$. [Image] The example of the carousel for $n=9$ and $t=[5, 5, 1, 15, 1, 5, 5, 1, 1]$. 

You want to color each figure in one of the colors. You think that it's boring if the carousel contains two different figures (with the distinct types of animals) going one right after another and colored in the same color.

Your task is to color the figures in such a way that the number of distinct colors used is the minimum possible and there are no figures of the different types going one right after another and colored in the same color. If you use exactly $k$ distinct colors, then the colors of figures should be denoted with integers from $1$ to $k$.

-----Input-----

The input contains one or more test cases.

The first line contains one integer $q$ ($1 \le q \le 10^4$) — the number of test cases in the test. Then $q$ test cases follow. One test case is given on two lines.

The first line of the test case contains one integer $n$ ($3 \le n \le 2 \cdot 10^5$) — the number of figures in the carousel. Figures are numbered from $1$ to $n$ in order of carousel moving. Assume that after the $n$-th figure the figure $1$ goes.

The second line of the test case contains $n$ integers $t_1, t_2, \dots, t_n$ ($1 \le t_i \le 2 \cdot 10^5$), where $t_i$ is the type of the animal of the $i$-th figure.

The sum of $n$ over all test cases does not exceed $2\cdot10^5$.

-----Output-----

Print $q$ answers, for each test case print two lines.

In the first line print one integer $k$ — the minimum possible number of distinct colors of figures.

In the second line print $n$ integers $c_1, c_2, \dots, c_n$ ($1 \le c_i \le k$), where $c_i$ is the color of the $i$-th figure. If there are several answers, you can print any.

-----Example-----
Input
4
5
1 2 1 2 2
6
1 2 2 1 2 2
5
1 2 1 2 3
3
10 10 10

Output
2
1 2 1 2 2
2
2 1 2 1 2 1
3
2 3 2 3 1
1
1 1 1
-/

-- <vc-helpers>
-- </vc-helpers>

def solve_carousel_coloring (n : Nat) (types : List Nat) : CarouselResult :=
  sorry

theorem color_count_valid {n : Nat} {types : List Nat}
  (h1 : n > 0) (h2 : types.length = n) :
  let result := solve_carousel_coloring n types
  result.colorCount ≤ 3 ∧ 
  ∀ c ∈ result.colors, 1 ≤ c ∧ c ≤ result.colorCount := 
  sorry

theorem output_length {n : Nat} {types : List Nat} 
  (h1 : n > 0) (h2 : types.length = n) :
  (solve_carousel_coloring n types).colors.length = n :=
  sorry

theorem same_type_same_color {n : Nat} {types : List Nat}
  (h1 : n > 0) (h2 : types.length = n)
  (h3 : ∀ i j, i < types.length → j < types.length → types[i]! = types[j]!) :
  let result := solve_carousel_coloring n types
  result.colorCount = 1 ∧ 
  ∀ c ∈ result.colors, c = 1 :=
  sorry

theorem even_length_alternating {n : Nat}
  (h1 : n > 1) (h2 : n % 2 = 0) :
  let types := List.join (List.replicate (n/2) [1,2])
  let result := solve_carousel_coloring n types
  result.colorCount = 2 ∧ result.colors.length = n :=
  sorry

/-
info: n1
-/
-- #guard_msgs in
-- #eval len colors1

/-
info: n2
-/
-- #guard_msgs in
-- #eval len colors2

-- Apps difficulty: introductory
-- Assurance level: unguarded