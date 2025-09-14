// <vc-preamble>
function power(x: real, n: nat) : real
  decreases n
{
    if n == 0 then 1.0 else x * power(x, n-1)
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method powerIter(x: real, n: nat) returns (p : real)
  ensures p == power(x, n)
// </vc-spec>
// <vc-code>
{
  p := 1.0;
  var i: nat := 0;
  while i < n
    invariant 0 <= i <= n
    invariant p == power(x, i)
    decreases n - i
  {
    p := p * x;
    i := i + 1;
  }
}
// </vc-code>
