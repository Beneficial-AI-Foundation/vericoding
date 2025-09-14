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
  var r: nat := 1;
  var i: nat := 1;
  while i <= n
    invariant i <= n + 1
    invariant r == fact(i - 1)
  {
    r := r * i;
    i := i + 1;
  }
  return r;
}
// </vc-code>

