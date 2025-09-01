

// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(n: nat) returns (r: nat)
  // post-conditions-start
  ensures r == popcount(n)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  if n == 0 {
    r := 0;
  } else {
    r := (n % 2) + popcount(n / 2);
  }
}
// </vc-code>

function popcount(n: nat): nat {
  if n == 0 then 0 else n % 2 + popcount(n / 2)
}
// pure-end