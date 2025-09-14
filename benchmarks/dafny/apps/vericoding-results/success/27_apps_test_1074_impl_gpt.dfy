function CountOnesInOctal(a: int): int
    requires a >= 0
{
    if a == 0 then 0
    else (if a % 8 == 1 then 1 else 0) + CountOnesInOctal(a / 8)
}

// <vc-helpers>
lemma Div8Decreases(x: int)
  requires x > 0
  ensures x / 8 < x
{
  var q := x / 8;
  var r := x % 8;
  assert 8 > 0;
  assert 0 <= r;
  assert r < 8;
  assert x == 8 * q + r;
  if q == 0 {
    assert 0 < x;
  } else {
    assert q >= 1;
    assert q < 8 * q;
    assert 8 * q <= x;
    assert q < x;
  }
}

lemma UnfoldCountOnesInOctalNonZero(x: int)
  requires x > 0
  ensures CountOnesInOctal(x) == (if x % 8 == 1 then 1 else 0) + CountOnesInOctal(x / 8)
{
  if x == 0 {
  } else {
    assert CountOnesInOctal(x) == (if x % 8 == 1 then 1 else 0) + CountOnesInOctal(x / 8);
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
  var x := a;
  var c := 0;
  while x != 0
    invariant x >= 0
    invariant c >= 0
    invariant c + CountOnesInOctal(x) == CountOnesInOctal(a)
    decreases x
  {
    assert x > 0;
    var add := if x % 8 == 1 then 1 else 0;
    assert add >= 0;
    UnfoldCountOnesInOctalNonZero(x);
    Div8Decreases(x);
    c := c + add;
    x := x / 8;
  }
  count := c;
  assert CountOnesInOctal(x) == 0;
}
// </vc-code>

