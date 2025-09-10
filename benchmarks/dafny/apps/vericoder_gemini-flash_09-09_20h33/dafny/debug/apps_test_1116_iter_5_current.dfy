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
lemma lemma_gcd_properties(a: int, b: int)
  requires a > 0 && b > 0
  ensures gcd(a, b) == gcd(b, a % b)
  ensures gcd(a, b) <= a
  ensures gcd(a, b) <= b
{
  if b != 0 {
    lemma_gcd_properties(b, a % b);
  }
}

lemma lemma_max_consecutive(r: int, b: int)
  requires r > 0 && b > 0
  ensures MaxConsecutiveSameColor(r, b) >= 0 // The number of consecutive same colors should be non-negative
{
  var a_val := if r <= b then r else b;
  var b_val := if r <= b then b else r;
  var n := gcd(a_val, b_val); // This n is the 'least common multiple' type value in the context of the problem, where string 'rb' repeats.
                             // More precisely, the period of the sequence is a_val + b_val / gcd(a_val, b_val).
                             // The formula for MaxConsecutiveSameColor seems to be derived from a specific problem context.
                             // Let's ensure the formula always returns a non-negative value.

  // Using properties of gcd: gcd(a,b) divides both a and b.
  // So, b_val is a multiple of n, and r/n or b/n are integers.
  // The expression is -((n - b_val) / a_val) = (b_val - n) / a_val.
  // Since n <= b_val (gcd is at most the smaller of the two numbers),
  // (b_val - n) >= 0.
  // Since a_val > 0, the result is >= 0.
}
// </vc-helpers>

// <vc-spec>
method solve(r: int, b: int, k: int) returns (result: string)
  requires ValidInput(r, b, k)
  ensures result == (if CanAvoidConsecutive(r, b, k) then "OBEY" else "REBEL")
// </vc-spec>
// <vc-code>
{
    if CanAvoidConsecutive(r, b, k) then {
        result := "OBEY";
    } else {
        result := "REBEL";
    }
}
// </vc-code>

