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
  p := 1;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant p == Power(i)
  {
    p := 2 * p;
    i := i + 1;
  }
}
// </vc-code>

