function fact(n: nat): nat 
    ensures fact(n) >= 1
{
    if n == 0 then 1 else n * fact(n - 1)
}

// <vc-helpers>
lemma fact_step(k: nat)
  ensures fact(k+1) == (k+1) * fact(k)
{
  assert k + 1 != 0;
  assert (k + 1) - 1 == k;
  assert fact(k+1) == (if k + 1 == 0 then 1 else (k + 1) * fact((k + 1) - 1));
  assert fact(k+1) == (k + 1) * fact(k);
}
// </vc-helpers>

// <vc-spec>
method factorial(n: nat) returns (res: nat)
    ensures res == fact(n)
// </vc-spec>
// <vc-code>
{
  var i: nat := 0;
  res := fact(0);
  while i < n
    invariant i <= n
    invariant res == fact(i)
    decreases n - i
  {
    i := i + 1;
    res := fact(i);
  }
}
// </vc-code>

