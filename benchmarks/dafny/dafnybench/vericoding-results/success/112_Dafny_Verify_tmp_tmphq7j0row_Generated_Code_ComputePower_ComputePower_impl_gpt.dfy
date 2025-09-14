function Power(n: nat): nat {
    if n == 0 then 1 else 2 * Power(n - 1)
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method ComputePower(n: nat) returns (p: nat)
    ensures p == Power(n)
// </vc-spec>
// <vc-code>
{
  var i: nat := 0;
  p := 1;
  while i < n
    invariant i <= n
    invariant p == Power(i)
    decreases n - i
  {
    assert Power(i + 1) == 2 * Power(i);
    p := 2 * p;
    i := i + 1;
  }
}
// </vc-code>

