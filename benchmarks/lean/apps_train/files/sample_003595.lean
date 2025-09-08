/-
## Task

You have to write three functions namely - `PNum, GPNum and SPNum` (JS, Coffee), `p_num, g_p_num and s_p_num` (Python and Ruby), `pNum, gpNum and spNum` (Java, C#), `p-num, gp-num and sp-num` (Clojure) - to check whether a given argument `n` is a Pentagonal, Generalized Pentagonal, or Square Pentagonal Number, and return `true` if it is and `false` otherwise.

### Description

`Pentagonal Numbers` - The nth pentagonal number Pn is the number of distinct dots in a pattern of dots consisting of the outlines of regular pentagons with sides up to n dots (means the side contains n number of dots), when the pentagons are overlaid so that they share one corner vertex.

> First few Pentagonal Numbers are: 1, 5, 12, 22...

`Generalized Pentagonal Numbers` - All the Pentagonal Numbers along with the number of dots inside the outlines of all the pentagons of a pattern forming a pentagonal number pentagon are called Generalized Pentagonal Numbers.

> First few Generalized Pentagonal Numbers are: 0, 1, 2, 5, 7, 12, 15, 22...

`Square Pentagonal Numbers` - The numbers which are Pentagonal Numbers and are also a perfect square are called Square Pentagonal Numbers. 

> First few are: 1, 9801, 94109401...

### Examples

#### Note: 
* Pn = Nth Pentagonal Number
* Gpn = Nth Generalized Pentagonal Number

     ^        ^          ^             ^                 ^
    P1=1     P2=5      P3=12         P4=22             P5=35   //Total number of distinct dots used in the Pattern
    Gp2=1    Gp4=5     Gp6=12        Gp8=22                    //All the Pentagonal Numbers are Generalised
             Gp1=0     Gp3=2         Gp5=7             Gp7=15  //Total Number of dots inside the outermost Pentagon
-/

def p_num (n : Int) : Bool := sorry
def g_p_num (n : Int) : Bool := sorry

def s_p_num (n : Int) : Bool := sorry

/- Helper function for pentagonal numbers -/

def pen (n : Int) : Int := (3*n*n - n) / 2

/- Helper function for generalized pentagonal numbers -/

-- <vc-helpers>
-- </vc-helpers>

def gen_pen (n : Int) : Int :=
  if n >= 0 then (3*n*n - n) / 2 else (3*n*n + n) / 2

theorem g_p_num_for_gen_pen (n : Int) : g_p_num (gen_pen n) = true := sorry

theorem s_p_num_is_square_of_pentagonal_number {n : Int} (h : s_p_num n = true) : 
  ∃ k : Int, 
    k * k = n ∧ 
    p_num k = true ∧
    g_p_num n = true := sorry

theorem non_square_not_s_p_num {n : Int} (h : ¬∃ k : Int, k * k = n) : 
  s_p_num n = false := sorry

/-
info: False
-/
-- #guard_msgs in
-- #eval p_num 0

/-
info: True
-/
-- #guard_msgs in
-- #eval p_num 1

/-
info: True
-/
-- #guard_msgs in
-- #eval p_num 5

/-
info: False
-/
-- #guard_msgs in
-- #eval p_num 100

/-
info: True
-/
-- #guard_msgs in
-- #eval g_p_num 0

/-
info: True
-/
-- #guard_msgs in
-- #eval g_p_num 1

/-
info: True
-/
-- #guard_msgs in
-- #eval g_p_num 2

/-
info: True
-/
-- #guard_msgs in
-- #eval g_p_num 5

/-
info: True
-/
-- #guard_msgs in
-- #eval s_p_num 1

/-
info: True
-/
-- #guard_msgs in
-- #eval s_p_num 9801

/-
info: False
-/
-- #guard_msgs in
-- #eval s_p_num 100

-- Apps difficulty: introductory
-- Assurance level: unguarded