// <vc-helpers>
function PopCount(n: nat): nat {
  if n == 0 then 0 else n % 2 + PopCount(n / 2)
}
// </vc-helpers>

// <vc-spec>
method solve(n: nat) returns (r: nat)
  // post-conditions-start
  ensures r == popcount(n)
  // post-conditions-end
// </vc-spec>
// <vc-code>
method Solve(n: nat) returns (r: nat)
  ensures r == PopCount(n)
{
  r := 0;
  var temp := n;
  while temp > 0
    invariant r + PopCount(temp) == PopCount(n)
  {
    r := r + temp % 2;
    temp := temp / 2;
  }
}
// </vc-code>

function popcount(n: nat): nat {
  if n == 0 then 0 else n % 2 + popcount(n / 2)
}
// pure-end