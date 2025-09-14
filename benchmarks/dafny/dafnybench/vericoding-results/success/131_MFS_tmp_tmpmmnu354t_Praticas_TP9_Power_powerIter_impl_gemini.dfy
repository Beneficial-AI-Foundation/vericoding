// <vc-preamble>
function power(x: real, n: nat) : real
{
    if n == 0 then 1.0 else x * power(x, n-1)
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method powerIter(b: real, n: nat) returns (p : real)
    ensures p == power(b, n)
// </vc-spec>
// <vc-code>
{
  p := 1.0;
  var i: nat := 0;
  while i < n
    invariant i <= n
    invariant p == power(b, i)
  {
    p := p * b;
    i := i + 1;
  }
}
// </vc-code>
