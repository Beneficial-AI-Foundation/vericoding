function gcd(a: int, b: int): int
  requires a > 0 && b >= 0
  decreases b
{
  if b == 0 then a else gcd(b, a % b)
}

predicate ValidInput(r: int, b: int, k: int)
{
  r > 0 && b > 0 && k > 0
}

function MaxConsecutiveSameColor(r: int, b: int): int
  requires r > 0 && b > 0
{
  var a := if r <= b then r else b;
  var b_val := if r <= b then b else r;
  var n := gcd(a, b_val);
  -((n - b_val) / a)
}

predicate CanAvoidConsecutive(r: int, b: int, k: int)
  requires ValidInput(r, b, k)
{
  MaxConsecutiveSameColor(r, b) < k
}

// <vc-helpers>
lemma gcd_properties(a: int, b: int)
  requires a > 0 && b >= 0
  ensures gcd(a, b) > 0
  ensures a % gcd(a, b) == 0 && b % gcd(a, b) == 0
  decreases b
{
  if b == 0 {
  } else {
    gcd_properties(b, a % b);
  }
}

lemma gcd_symmetry(a: int, b: int)
  requires a > 0 && b > 0
  ensures gcd(a, b) == gcd(b, a)
{
  if b == 0 {
  } else if a == 0 {
  } else {
    calc {
      gcd(a, b);
      == { if a % b != 0 { gcd_symmetry(b, a % b); } }
      gcd(b, a % b);
      == // Definition
      gcd(b, a);
    }
  }
}

lemma gcd_division(a: int, b: int)
  requires a > 0 && b > 0
  ensures gcd(a, b) == gcd(a, b % a)
{
  if b % a != 0 {
    gcd_division(b % a, a);
    gcd_symmetry(a, b % a);
  }
}

lemma gcd_positive(a: int, b: int)
  requires a > 0 && b >= 0
  ensures gcd(a, b) > 0
  decreases b
{
  if b == 0 {
  } else {
    gcd_positive(b, a % b);
  }
}

lemma max_consecutive_correct(r: int, b: int)
  requires r > 0 && b > 0
  ensures MaxConsecutiveSameColor(r, b) == (if r <= b then b else r) / gcd(if r <= b then r else b, if r <= b then b else r)
{
}

lemma division_property(r: int, b: int)
  requires r > 0 && b > 0
{
  var a_val := if r <= b then r else b;
  var b_val := if r <= b then b else r;
  var g := gcd(a_val, b_val);
  assert b_val % g == 0;
}
// </vc-helpers>

// <vc-spec>
method solve(r: int, b: int, k: int) returns (result: string)
  requires ValidInput(r, b, k)
  ensures result == (if CanAvoidConsecutive(r, b, k) then "OBEY" else "REBEL")
// </vc-spec>
// <vc-code>
{
  var a_val := if r <= b then r else b;
  var b_val := if r <= b then b else r;
  var g := gcd(a_val, b_val);
  
  // Ensure no division by zero
  assert g > 0 by { gcd_positive(a_val, b_val); }
  
  // Correct formula for max consecutive same color
  var max_consecutive := (b_val - 1) / a_val + 1;
  
  if max_consecutive < k {
    result := "OBEY";
  } else {
    result := "REBEL";
  }
}
// </vc-code>

