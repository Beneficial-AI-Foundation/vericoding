/-
Kajaria has an empty bag and 2 types of tiles - 
tiles of type $1$ have the number $X$ written and those of type $2$ have the number $Y$ written on them. He has an infinite supply of both type of tiles.
In one move, Kajaria adds exactly $1$ tile to the bag. He adds a tile of type $1$ with probability $p$ and a tile of type $2$ with probability $(1 - p)$.
If $2$ tiles in the bag have the same number written on them (say $Z$), they are merged into a single tile of twice that number ($2Z$).
Find the expected number of moves to reach the first tile with number $S$ written on it.
Notes on merging: 
- Consider that the bag contains tiles $(5, 10, 20, 40)$ and if the new tile added is $5$, then it would merge with the existing $5$ and the bag would now contain $(10, 10, 20, 40)$. The tiles $10$ (already present) and $10$ (newly formed) would then merge in the same move to form $(20, 20, 40)$, and that will form $(40, 40)$, which will form $(80)$.
Kajaria guarantees that:
- $X$ and $Y$ are not divisible by each other.
- A tile with number $S$ can be formed.

-----Input-----
- First line contains a single integer $T$ - the total no. of testcases
- Each testcase is described by $2$ lines:
- $X, Y, S$ - $3$ space-separated natural numbers
- $u, v$ - $2$ space-separated natural numbers describing the probability $p$
The value of $p$ is provided as a fraction in its lowest form $u/v$ ($u$ and $v$ are co-prime)

-----Output-----
- For each testcase, if the expected number of moves can be expressed as a fraction $p/q$ in its lowest form, print $(p * q^{-1})$ modulo $10^9 + 7$, where $q^{-1}$ denotes the modular inverse of $q$ wrt $10^9 + 7$.

-----Constraints-----
- $1 \leq T \leq 10^5$
- $2 \leq X, Y \leq 5 * 10^{17}$
- $1 \leq S \leq 10^{18}$
- $1 \leq u < v \leq 10^{9}$

-----Sample Input-----
1
5 3 96
1 3

-----Sample Output-----
48
-/

-- <vc-helpers>
-- </vc-helpers>

def solve_tile_expectation (x y s u v : Nat) : Nat :=
  sorry

theorem output_bounds {x y s u v : Nat} (x_prime : x ∈ [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]) 
    (y_prime : y ∈ [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31])
    (s_bound : 1 ≤ s ∧ s ≤ 10^9)
    (u_bound : 1 ≤ u ∧ u ≤ 10^9) 
    (v_bound : 1 ≤ v ∧ v ≤ 10^9)
    (v_greater : u < v) :
    let result := solve_tile_expectation x y s u v
    0 ≤ result ∧ result < 1000000007 :=
  sorry

/-
info: 48
-/
-- #guard_msgs in
-- #eval solve_tile_expectation 5 3 96 1 3

/-
info: 24
-/
-- #guard_msgs in
-- #eval solve_tile_expectation 5 3 48 1 3

/-
info: 96
-/
-- #guard_msgs in
-- #eval solve_tile_expectation 5 3 192 1 3

-- Apps difficulty: interview
-- Assurance level: guarded