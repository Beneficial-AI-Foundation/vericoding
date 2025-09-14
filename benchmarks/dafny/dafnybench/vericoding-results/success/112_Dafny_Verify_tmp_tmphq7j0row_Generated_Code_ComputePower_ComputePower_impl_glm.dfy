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
  var result: nat := 1;
  while i < n
    invariant result == Power(i)
    invariant i <= n
  {
    result := result * 2;
    i := i + 1;
  }
  return result;
}
// </vc-code>

