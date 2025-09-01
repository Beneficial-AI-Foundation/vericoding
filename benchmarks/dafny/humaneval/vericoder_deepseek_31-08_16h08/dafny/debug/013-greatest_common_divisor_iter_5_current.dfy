// recursive version should be more promising

// <vc-helpers>
lemma GcdPositive(a: int, b: int)
  requires a != 0 || b != 0
  ensures gcd(a, b) != 0
  decreases if a < 0 then -a else a, if b < 0 then -b else b
{
  if a == 0 {
  } else if b == 0 {
  } else if a > b {
    GcdPositive(a - b, b);
  } else {
    GcdPositive(a, b - a);
  }
}

function gcd(a: int, b: int): int
  requires a != 0 || b != 0
  decreases if a < 0 then -a else a, if b < 0 then -b else b
{
  if a == 0 then (if b < 0 then -b else b)
  else if b == 0 then (if a < 0 then -a else a)
  else if a > b then gcd(a - b, b)
  else gcd(a, b - a)
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method greatest_common_divisor(a: int, b: int) returns (gcd: int)
    // pre-conditions-start
    requires a != 0 || b != 0
    // pre-conditions-end
    // post-conditions-start
    ensures gcd != 0
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var abs_a := if a < 0 then -a else a;
  var abs_b := if b < 0 then -b else b;
  
  if abs_a == 0 {
    gcd := abs_b;
  } else if abs_b == 0 {
    gcd := abs_a;
  } else {
    var x := abs_a;
    var y := abs_b;
    while y != 0
      decreases y
    {
      var t := y;
      y := x % y;
      x := t;
    }
    gcd := x;
  }
  GcdPositive(a, b);
}
// </vc-code>

