

// <vc-helpers>
function SumUpTo(k: int): int
  requires k >= 0
  ensures SumUpTo(k) == k * (k + 1) / 2
{
  if k == 0 then 0
  else k + SumUpTo(k - 1)
}
// </vc-helpers>

// <vc-spec>
method sum_to_n(n: int) returns (r : int)
  // post-conditions-start
  ensures r == n * (n + 1) / 2
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var sum := 0;
  while i <= n
    invariant sum == i * (i + 1) / 2
    invariant 0 <= i <= n + 1
  {
    sum := sum + i + 1; // sum should be sum of (0 to i) and next iteration it adds current i+1, so after that sum becomes sum of (0 to i+1)
    i := i + 1;
  }
  return sum;
}
// </vc-code>

