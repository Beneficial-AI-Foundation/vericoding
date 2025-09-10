

// <vc-helpers>
lemma LargestDivisorCorrect(n: int, i: int, d: int)
  requires n > 1
  requires 2 <= i < n
  requires n % i == 0
  requires d == n / i
  requires forall k :: 2 <= k < i ==> n % k != 0
  ensures 1 <= d < n
  ensures n % d == 0
  ensures forall k :: d < k < n ==> n % k != 0
{
  assert d * i == n;
  assert d >= 1;
  assert d < n;
  assert n % d == 0;
  
  forall k | d < k < n
    ensures n % k != 0
  {
    if n % k == 0 {
      var j := n / k;
      assert j * k == n;
      assert j >= 1;
      
      // Key insight: k > d = n/i implies j < i
      assert k > n/i;
      assert k * i > n;
      assert n/k < i;
      assert j < i;
      
      // Also j >= 2 since k < n
      assert k < n;
      assert n/k > 1;
      assert j > 1;
      assert j >= 2;
      
      assert n % j == 0;
      assert 2 <= j < i;
      assert false;
    }
  }
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
  var i := 2;
  while i < n
    invariant 2 <= i <= n
    invariant forall k :: 2 <= k < i ==> n % k != 0
  {
    if n % i == 0 {
      d := n / i;
      LargestDivisorCorrect(n, i, d);
      return;
    }
    i := i + 1;
  }
  d := 1;
}
// </vc-code>

