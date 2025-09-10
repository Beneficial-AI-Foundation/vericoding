function CountOnesInOctal(a: int): int
    requires a >= 0
{
    if a == 0 then 0
    else (if a % 8 == 1 then 1 else 0) + CountOnesInOctal(a / 8)
}

// <vc-helpers>

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
  count := 0;
  while x > 0
    invariant x >= 0
    invariant count >= 0
    invariant count + CountOnesInOctal(x) == CountOnesInOctal(a)
    decreases x
  {
    var oldCount := count;
    if x % 8 == 1 {
      count := count + 1;
    }
    assert count == oldCount + (if x % 8 == 1 then 1 else 0);
    assert x > 0;
    assert CountOnesInOctal(x) == (if x % 8 == 1 then 1 else 0) + CountOnesInOctal(x / 8);
    assert count + CountOnesInOctal(x / 8) == oldCount + CountOnesInOctal(x);
    x := x / 8;
  }
  assert CountOnesInOctal(0) == 0;
}
// </vc-code>

