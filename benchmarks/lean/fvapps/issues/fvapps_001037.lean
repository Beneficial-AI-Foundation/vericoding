-- <vc-preamble>
def absInt (n : Int) : Int :=
  if n ≥ 0 then n else -n
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Animal.will_collide : Animal → Animal → Option Float := sorry

def solve : Int → Int → List (Int × Int × Int) → List (Int × Int × Int) → List Int := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem animal_init_properties (start endpoint starting_time : Int) (a : Animal) 
    (h : a = Animal.mk start endpoint starting_time sorry sorry sorry) :
  a.ending_time = starting_time + absInt (start - endpoint) ∧
  (a.velocity = 1 ∨ a.velocity = -1) ∧
  (endpoint ≥ start → a.velocity = 1) ∧
  (endpoint < start → a.velocity = -1) ∧
  a.eaten_by = (Int.neg 1, 10000000000) := sorry

theorem solve_output_properties (n m : Int) (cats rats : List (Int × Int × Int)) 
    (hn : n > 0) (hm : m > 0) :
  let result := solve n m cats rats
  List.length result = m ∧ 
  ∀ r ∈ result, -1 ≤ r ∧ r ≤ n := sorry

theorem collision_symmetry (s1 e1 t1 s2 e2 t2 : Int) :
  let a1 := Animal.mk s1 e1 t1 sorry sorry sorry
  let a2 := Animal.mk s2 e2 t2 sorry sorry sorry
  match a1.will_collide a2, a2.will_collide a1 with
  | some x, some y => Float.abs (x - y) < 0.0000000001
  | none, none => True
  | _, _ => False := sorry

theorem self_collision (start endpoint time : Int) :
  let animal := Animal.mk start endpoint time sorry sorry sorry
  match animal.will_collide animal with
  | some t => Float.toUInt64 t ≥ Float.toUInt64 (Float.ofInt time) ∧ 
              Float.toUInt64 t ≤ Float.toUInt64 (Float.ofInt animal.ending_time)  
  | none => True := sorry
-- </vc-theorems>