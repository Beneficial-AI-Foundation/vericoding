/-
Find the sum of the odd numbers within an array, after cubing the initial integers. The function should return `undefined`/`None`/`nil`/`NULL` if any of the values aren't numbers. 

~~~if:java,csharp
Note: There are ONLY integers in the JAVA and C# versions of this Kata.
~~~

~~~if:python
Note: Booleans should not be considered as numbers.
~~~
-/

-- <vc-helpers>
-- </vc-helpers>

def cube_odd (xs : List Int) : Int :=
  sorry

theorem cube_odd_integers (xs : List Int) :
  cube_odd xs = (xs.filter (fun x => x % 2 ≠ 0)
                |>.map (fun x => x * x * x)
                |>.foldl (· + ·) 0 : Int)
  := sorry

theorem cube_odd_bounded (xs : List Int) 
  (h : ∀ x ∈ xs, -1000 ≤ x ∧ x ≤ 1000) :
  cube_odd xs = (xs.filter (fun x => x % 2 ≠ 0)
                |>.map (fun x => x * x * x)
                |>.foldl (· + ·) 0 : Int)
  := sorry

theorem cube_odd_non_empty (xs : List Int)
  (h : xs ≠ []) : 
  cube_odd xs = (xs.filter (fun x => x % 2 ≠ 0)
                |>.map (fun x => x * x * x)
                |>.foldl (· + ·) 0 : Int)
  := sorry

/-
info: 28
-/
-- #guard_msgs in
-- #eval cube_odd [1, 2, 3, 4]

/-
info: 0
-/
-- #guard_msgs in
-- #eval cube_odd [-3, -2, 2, 3]

/-
info: None
-/
-- #guard_msgs in
-- #eval cube_odd ["a", 12, 9, "z", 42]

-- Apps difficulty: introductory
-- Assurance level: unguarded