// <vc-helpers>
lemma DivisorLemma(n: int, d: int)
  requires n > 1
  requires 1 <= d < n
  requires n % d == 0
  ensures exists k :: 1 <= k <= d && n % k == 0
{
}
// </vc-helpers>

// <vc-spec>
method largest_divisor(n: int) returns (d : int)
  // pre-conditions-start
  requires n > 1
  // pre-conditions-end
  // post-conditions-start
  ensures 1 <= d < n
  ensures n % d == 0
  ensures forall k :: d < k < n ==> n % k != 0
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var i := n - 1;
  while i > 1
    decreases i
    invariant 1 <= i < n
    invariant forall k :: i < k < n ==> n % k != 0
  {
    if n % i == 0 {
      return i;
    }
    i := i - 1;
  }
  return 1;
}
// </vc-code>
