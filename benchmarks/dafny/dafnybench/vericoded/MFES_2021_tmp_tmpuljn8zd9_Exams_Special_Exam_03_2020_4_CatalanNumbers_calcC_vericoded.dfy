function C(n: nat): nat 
    decreases n
{
    if n == 0 then 1 else (4 * n - 2) * C(n-1) / (n + 1) 
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method calcC(n: nat) returns (res: nat)
    ensures res == C(n)
// </vc-spec>
// <vc-code>
{
  var i := 0;
  res := 1;
  while i < n
    invariant 0 <= i <= n
    invariant res == C(i)
    decreases n - i
  {
    res := C(i + 1);
    i := i + 1;
  }
}
// </vc-code>

