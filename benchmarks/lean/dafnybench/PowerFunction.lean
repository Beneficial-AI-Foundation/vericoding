/-
  Port of cs245-verification_tmp_tmp0h_nxhqp_A8_Q1_spec.dfy
  
  This specification describes computing x to the power of y0.
  The function takes:
  - y0: A non-negative exponent
  - x: The base
  
  Returns z = x^y0
-/

namespace DafnyBenchmarks

/-- Power function for specification -/
def power (a : Int) (n : Nat) : Int :=
  match n with
  | 0 => 1
  | n + 1 => a * power a n

/-- Compute x to the power of y0 -/
def computePower (y0 : Nat) (x : Int) : Int :=
  let rec loop (y : Nat) (z : Int) : Int :=
    match y with
    | 0 => z
    | y + 1 => loop y (z * x)
  loop y0 1

/-- Specification for computePower -/
theorem computePower_spec (y0 : Nat) (x : Int) :
    computePower y0 x = power x y0 := by
  sorry

end DafnyBenchmarks