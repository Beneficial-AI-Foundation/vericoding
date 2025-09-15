// <vc-preamble>
function popcount(n: nat): nat {
  if n == 0 then 0 else n % 2 + popcount(n / 2)
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(n: nat) returns (r: nat)

  ensures r == popcount(n)
// </vc-spec>
// <vc-code>
{
  r := 0;
  var i := n;
  while i > 0
    invariant r + popcount(i) == popcount(n)
    decreases i
  {
    r := r + (i % 2);
    i := i / 2;
  }
}
// </vc-code>
