// I can implement this using repeated addition, where I add `m` to itself `n` times. I'll use a loop with appropriate loop invariants to ensure verification.

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method CalcProduct(m: nat, n: nat) returns (res: nat)
  ensures res == m*n;
// </vc-spec>
// <vc-code>
{
  res := 0;
  var i := 0;
  
  while i < n
    invariant 0 <= i <= n
    invariant res == m * i
  {
    res := res + m;
    i := i + 1;
  }
}
// </vc-code>