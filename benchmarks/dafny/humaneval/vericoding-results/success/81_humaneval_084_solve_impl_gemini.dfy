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
  var x := n;
  while x > 0
    invariant popcount(n) == r + popcount(x)
  {
    r := r + x % 2;
    x := x / 2;
  }
}
// </vc-code>
