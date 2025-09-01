

// <vc-helpers>
function popcount(n: nat): nat {
  if n == 0 then 0 else n % 2 + popcount(n / 2)
}
// </vc-helpers>

// <vc-spec>
method solve(n: nat) returns (r: nat)
  // post-conditions-start
  ensures r == popcount(n)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var count := 0;
  var temp_n := n;

  while temp_n > 0
    invariant count + popcount(temp_n) == popcount(n)
    decreases temp_n
  {
    if temp_n % 2 == 1 {
      count := count + 1;
    }
    temp_n := temp_n / 2;
  }
  return count;
}
// </vc-code>

function popcount(n: nat): nat {
  if n == 0 then 0 else n % 2 + popcount(n / 2)
}
// pure-end