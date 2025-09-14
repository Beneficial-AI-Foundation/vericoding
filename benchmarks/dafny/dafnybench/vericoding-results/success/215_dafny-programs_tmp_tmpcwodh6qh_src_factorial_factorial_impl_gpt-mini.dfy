function fact(n: nat): nat 
    ensures fact(n) >= 1
{
    if n == 0 then 1 else n * fact(n - 1)
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method factorial(n: nat) returns (res: nat)
    ensures res == fact(n)
// </vc-spec>
// <vc-code>
{
  var k := 0;
  var prod := 1;
  // Invariant: prod == fact(k) and k in [0..n]
  while k < n
    decreases n - k
    invariant 0 <= k <= n
    invariant prod == fact(k)
  {
    k := k + 1;
    prod := prod * k;
  }
  res := prod;
}
// </vc-code>

