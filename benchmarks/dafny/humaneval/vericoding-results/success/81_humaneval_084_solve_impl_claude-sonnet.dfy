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
  var temp := n;
  while temp > 0
    invariant r + popcount(temp) == popcount(n)
    decreases temp
  {
    r := r + temp % 2;
    temp := temp / 2;
  }
}
// </vc-code>
