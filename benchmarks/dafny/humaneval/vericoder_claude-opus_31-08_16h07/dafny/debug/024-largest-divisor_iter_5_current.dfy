

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
  // Basic properties
  assert d * i == n;
  assert d >= 1 by {
    assert i < n;
    assert d * i == n;
    assert d >= 1;
  }
  assert d < n by {
    assert i >= 2;
    assert d * i == n;
    assert d <= n / 2;
  }
  assert n % d == 0;
  
  // For any k such that d < k < n and n % k == 0, we derive a contradiction
  forall k | d < k < n && n % k == 0
    ensures false
  {
    var j := n / k;
    assert j * k == n;
    
    // Since k > d = n/i, we have j < i
    calc {
      k > d;
    ==
      k > n / i;
    ==>
      k * i > n;
    ==>
      i > n / k;
    ==>
      i > j;
    }
    
    // Since k < n, we have j > 1
    assert j >= 2 by {
      assert k < n;
      assert j * k == n;
      assert j > 1;
    }
    
    // So j is a divisor with 2 <= j < i
    assert n % j == 0;
    assert 2 <= j < i;
    // This contradicts our assumption
    assert false;
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

