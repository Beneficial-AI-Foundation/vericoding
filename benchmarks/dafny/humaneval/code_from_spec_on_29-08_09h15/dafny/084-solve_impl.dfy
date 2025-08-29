

// <vc-helpers>
lemma PopcountProperties(n: nat)
  ensures popcount(n) >= 0
  ensures n > 0 ==> popcount(n) > 0 || popcount(n) == 0
{
  if n == 0 {
    assert popcount(n) == 0;
  } else {
    PopcountProperties(n / 2);
  }
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def solve(n: int) -> str
Given a positive integer N, return the total sum of its digits in binary.
*/
// </vc-description>

// <vc-spec>
method solve(n: nat) returns (r: nat)
  // post-conditions-start
  ensures r == popcount(n)
  // post-conditions-end
// </vc-spec>

// <vc-code>
{
  PopcountProperties(n);
  r := popcount(n);
}
// </vc-code>

function popcount(n: nat): nat {
  if n == 0 then 0 else n % 2 + popcount(n / 2)
}
// pure-end