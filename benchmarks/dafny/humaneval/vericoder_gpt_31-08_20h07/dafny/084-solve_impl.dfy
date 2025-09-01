

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
  var x: nat := n;
  var c: nat := 0;
  while x != 0
    invariant c + popcount(x) == popcount(n)
  {
    assert popcount(x) == x % 2 + popcount(x / 2);
    c := c + x % 2;
    x := x / 2;
  }
  r := c;
}
// </vc-code>

function popcount(n: nat): nat {
  if n == 0 then 0 else n % 2 + popcount(n / 2)
}
// pure-end