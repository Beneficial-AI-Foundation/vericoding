

// <vc-helpers>
lemma sqr_le_implies_le(k:int, n:int)
  requires n >= 0 && 0 <= k && k*k <= n
  ensures k <= n
{
  if k > n {
    // k >= n+1
    assert k >= n+1;
    // from k > n >= 0, we get k >= 1
    assert k >= 1;
    // multiply (n+1) by k >= 1 gives k*(n+1) >= n+1
    assert k*(n+1) >= n+1;
    // since n+1 <= k and k >= 0, multiply both sides by k to get k*(n+1) <= k*k
    assert k*(n+1) <= k*k;
    // hence k*k >= k*(n+1) >= n+1 > n, contradiction with k*k <= n
    assert k*k > n;
    assert false;
  }
}
// </vc-helpers>

// <vc-spec>
method mroot1(n:int) returns (r:int) //Cost O(root n)
requires n>=0
ensures r>=0 && r*r <= n <(r+1)*(r+1)
// </vc-spec>
// <vc-code>
{
  r := 0;
  while (r+1)*(r+1) <= n
    invariant r >= 0
    invariant r*r <= n
    invariant n - r >= 0
    decreases n - r
  {
    r := r + 1;
    // from r*r <= n and r >= 0 we can deduce r <= n
    sqr_le_implies_le(r, n);
  }
}
// </vc-code>

