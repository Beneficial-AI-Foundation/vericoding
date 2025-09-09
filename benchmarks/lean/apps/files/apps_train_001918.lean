/-
In the evenings Donkey would join Shrek to look at the stars. They would sit on a log, sipping tea and they would watch the starry sky. The sky hung above the roof, right behind the chimney. Shrek's stars were to the right of the chimney and the Donkey's stars were to the left. Most days the Donkey would just count the stars, so he knew that they are exactly n. This time he wanted a challenge. He imagined a coordinate system: he put the origin of the coordinates at the intersection of the roof and the chimney, directed the OX axis to the left along the roof and the OY axis — up along the chimney (see figure). The Donkey imagined two rays emanating from he origin of axes at angles α_1 and α_2 to the OX axis.

 [Image] 

Now he chooses any star that lies strictly between these rays. After that he imagines more rays that emanate from this star at the same angles α_1 and α_2 to the OX axis and chooses another star that lies strictly between the new rays. He repeats the operation as long as there still are stars he can choose between the rays that emanate from a star. 

 [Image] 

As a result, the Donkey gets a chain of stars. He can consecutively get to each star if he acts by the given rules.

Your task is to find the maximum number of stars m that the Donkey's chain can contain.

Note that the chain must necessarily start in the point of the origin of the axes, that isn't taken into consideration while counting the number m of stars in the chain.

-----Input-----

The first line contains an integer n (1 ≤ n ≤ 10^5) — the number of stars. The second line contains simple fractions representing relationships "a/b c/d", such that $\frac{a}{b} = \frac{\operatorname{sin} \alpha_{1}}{\operatorname{cos} \alpha_{1}}$ and $\frac{c}{d} = \frac{\operatorname{sin} \alpha_{2}}{\operatorname{cos} \alpha}$ (0 ≤ a, b, c, d ≤ 10^5; $0^{\circ} \leq \alpha_{1} < \alpha_{2} \leq 90^{\circ}$; $\frac{a}{b} \neq \frac{0}{0}$; $\frac{c}{d} \neq \frac{0}{0}$). The given numbers a, b, c, d are integers.

Next n lines contain pairs of integers x_{i}, y_{i} (1 ≤ x_{i}, y_{i} ≤ 10^5)— the stars' coordinates.

It is guaranteed that all stars have distinct coordinates.

-----Output-----

In a single line print number m — the answer to the problem.

-----Examples-----
Input
15
1/3 2/1
3 1
6 2
4 2
2 5
4 5
6 6
3 4
1 6
2 1
7 4
9 3
5 3
1 3
15 5
12 4

Output
4

-----Note-----

In the sample the longest chain the Donkey can build consists of four stars. Note that the Donkey can't choose the stars that lie on the rays he imagines.

 [Image]
-/

-- <vc-helpers>
-- </vc-helpers>

def find_max_stars (n : Nat) (a b c d : Int) (stars : List (Int × Int)) : Nat := sorry

theorem output_bounds {n : Nat} {a b c d : Int} {stars : List (Int × Int)}
  (h1 : n > 0) 
  (h2 : ¬(a = 0 ∧ b = 0))
  (h3 : ¬(c = 0 ∧ d = 0))
  (h4 : a * d ≠ b * c)
  (h5 : stars ≠ []) :
  let result := find_max_stars n a b c d stars
  result ≥ 0 ∧ result ≤ stars.length := by sorry

theorem identical_points {n : Nat} {a b c d : Int} {stars : List (Int × Int)}
  (h1 : n > 0)
  (h2 : ¬(a = 0 ∧ b = 0))
  (h3 : ¬(c = 0 ∧ d = 0)) 
  (h4 : a * d ≠ b * c)
  (h5 : stars ≠ []) :
  find_max_stars n a b c d stars = find_max_stars n a b c d (stars ++ stars) := by sorry

theorem empty_stars {n : Nat} {a b c d : Int}
  (h1 : n > 0)
  (h2 : ¬(a = 0 ∧ b = 0))
  (h3 : ¬(c = 0 ∧ d = 0))
  (h4 : a * d ≠ b * c) :
  find_max_stars n a b c d [] = 0 := by sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval find_max_stars 15 1 3 2 1 [(3, 1), (6, 2), (4, 2), (2, 5), (4, 5), (6, 6), (3, 4), (1, 6), (2, 1), (7, 4), (9, 3), (5, 3), (1, 3), (15, 5), (12, 4)]

/-
info: 3
-/
-- #guard_msgs in
-- #eval find_max_stars 5 3 24 24 3 [(31394, 23366), (27990, 71363), (33642, 36903), (79731, 10588), (10907, 5058)]

/-
info: 3
-/
-- #guard_msgs in
-- #eval find_max_stars 5 0 17 74 0 [(69711, 29703), (91677, 56040), (26051, 78244), (20816, 40897), (70770, 35908)]

-- Apps difficulty: competition
-- Assurance level: unguarded