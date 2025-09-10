

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(n: nat) returns (r: nat)
  // post-conditions-start
  ensures r == popcount(n)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  r := 0;
  var x := n;
  while x != 0
    invariant r + popcount(x) == popcount(n)
    decreases x
  {
    var bit := x % 2;
    r := r + bit;
    x := x / 2;
  }
}
// </vc-code>

function popcount(n: nat): nat {
  if n == 0 then 0 else n % 2 + popcount(n / 2)
}
// pure-end