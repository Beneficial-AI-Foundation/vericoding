function CountOnesInOctal(a: int): int
    requires a >= 0
{
    if a == 0 then 0
    else (if a % 8 == 1 then 1 else 0) + CountOnesInOctal(a / 8)
}

// <vc-helpers>
lemma Div8Less(x: int)
  ensures x > 0 ==> x / 8 < x
{
  if x > 0 {
    var q := x / 8;
    var r := x % 8;
    assert x == 8 * q + r;
    assert 0 <= r && r < 8;
    if q >= x {
      // 8*q >= 8*x
      assert 8 * q >= 8 * x;
      // but 8*q == x - r and r >= 0, so 8*q <= x
      assert 8 * q == x - r;
      assert 8 * q <= x;
      // hence 8*x <= x, so 7*x <= 0, contradicting x > 0
      assert 8 * x <= x;
      assert 7 * x <= 0;
      assert 7 * x > 0; // since x > 0
      assert false;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method solve(a: int) returns (count: int)
    requires a >= 0
    ensures count >= 0
    ensures count == CountOnesInOctal(a)
// </vc-spec>
// <vc-code>
{
  count := 0;
  var x := a;
  while x > 0
    invariant x >= 0
    invariant count >= 0
    invariant count + CountOnesInOctal(x) == CountOnesInOctal(a)
    decreases x
  {
    var oldx := x;
    var b := if x % 8 == 1 then 1 else 0;
    count := count + b;
    x := x / 8;
    Div8Less(oldx);
    assert x < oldx;
  }
}
// </vc-code>

