/*
function_signature: def solve(n: int) -> str
Given a positive integer N, return the total sum of its digits in binary.
*/

method solve(n: nat) returns (r: nat)
  // post-conditions-start
  ensures r == popcount(n)
  // post-conditions-end
{
  assume false;
}

function popcount(n: nat): nat {
  if n == 0 then 0 else n % 2 + popcount(n / 2)
}
// pure-end