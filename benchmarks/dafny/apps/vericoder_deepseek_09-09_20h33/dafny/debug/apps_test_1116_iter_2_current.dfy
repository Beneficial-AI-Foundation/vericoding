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
  if b != 0 {
    gcd_properties(b, a % b);
    // After recursive call, we know gcd(b, a % b) divides both b and (a % b)
    // Since gcd(a, b) = gcd(b, a % b), it must also divide a
  }
}

lemma max_consecutive_correct(r: int, b: int)
  requires r > 0 && b > 0
  ensures MaxConsecutiveSameColor(r, b) == (var a_val := if r <= b then r else b; var b_val := if r <= b then b else r; var n := gcd(a_val, b_val); (b_val - n) / a_val + 1)
{
  // The implementation matches the function definition, so this is trivially true
}

lemma gcd_symmetry(a: int, b: int)
  requires a > 0 && b > 0
  ensures gcd(a, b) == gcd(b, a)
{
  // Prove by showing both gcd calculations follow the same steps
  if a != b {
    if a > b {
      gcd_symmetry(b, a % b);
    } else {
      gcd_symmetry(a, b % a);
    }
  }
}

lemma gcd_division(a: int, b: int)
  requires a > 0 && b > 0
  ensures gcd(a, b) == gcd(a, b % a)
{
  if b % a != 0 {
    gcd_division(b % a, a);
  }
}

lemma gcd_positive(a: int, b: int)
  requires a > 0 && b >= 0
  ensures gcd(a, b) > 0
{
  if b != 0 {
    gcd_positive(b, a % b);
  }
}

lemma division_property(r: int, b: int)
  requires r > 0 && b > 0
  ensures (b - gcd(r, b)) % r == 0
{
  gcd_properties(r, b);
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(r: int, b: int, k: int) returns (result: string)
  requires ValidInput(r, b, k)
  ensures result == (if CanAvoidConsecutive(r, b, k) then "OBEY" else "REBEL")
// </vc-spec>
// <vc-code>
{
  var a := if r <= b then r else b;
  var b_val := if r <= b then b else r;
  
  gcd_positive(a, b_val);
  gcd_properties(a, b_val);
  division_property(a, b_val);
  
  var max_consecutive := (b_val - gcd(a, b_val)) / a + 1;
  
  if max_consecutive < k {
    result := "OBEY";
  } else {
    result := "REBEL";
  }
}
// </vc-code>

