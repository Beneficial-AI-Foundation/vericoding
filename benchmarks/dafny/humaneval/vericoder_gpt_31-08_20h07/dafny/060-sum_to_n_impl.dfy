

// <vc-helpers>
// <vc-helpers>

// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method sum_to_n(n: int) returns (r : int)
  // post-conditions-start
  ensures r == n * (n + 1) / 2
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  r := n * (n + 1) / 2;
}
// </vc-code>

