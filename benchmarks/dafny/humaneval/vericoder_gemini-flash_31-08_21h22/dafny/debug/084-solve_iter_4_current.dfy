

// <vc-helpers>
function popcount_helper(n: nat): nat {
  if n == 0 then 0 else n % 2 + popcount_helper(n / 2)
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
  var r_val := 0;
  var temp_n := n;

  while temp_n > 0
    invariant temp_n >= 0
    invariant r_val + popcount_helper(temp_n) == popcount_helper(n)
  {
    r_val := r_val + (temp_n % 2);
    temp_n := temp_n / 2;
  }
  return r_val;
}
// </vc-code>

function popcount(n: nat): nat {
  if n == 0 then 0 else n % 2 + popcount(n / 2)
}
// pure-end