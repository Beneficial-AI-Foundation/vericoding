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
  count := 0;
  var i := a;
  while i > 0
    invariant i >= 0
    invariant count + CountOnesInOctal(i) == CountOnesInOctal(a)
    decreases i
  {
    if i % 8 == 1 {
      count := count + 1;
    }
    i := i / 8;
  }
}
// </vc-code>

