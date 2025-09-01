

// <vc-helpers>
lemma LargestDivisorExists(n: int)
  requires n > 1
  ensures exists d :: 1 <= d < n && n % d == 0 && (forall k :: d < k < n ==> n % k != 0)
{
  var d := n - 1;
  while d >= 1
    invariant d >= 1
    invariant forall k :: d < k < n ==> n % k != 0
    decreases d
  {
    if n % d == 0 {
      return;
    }
    d := d - 1;
  }
  // When we reach d == 1, it's always a divisor
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
  var k := n - 1;
  while k >= 1
    invariant k >= 1
    invariant forall i :: k < i < n ==> n % i != 0
    decreases k
  {
    if n % k == 0 {
      d := k;
      return;
    }
    k := k - 1;
  }
  d := 1;
}
// </vc-code>

