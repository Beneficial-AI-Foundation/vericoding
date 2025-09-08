Find the smallest positive integer x such that (x div k) × (x mod k) = n,
where x div k is integer division and x mod k is the remainder.

predicate ValidInput(n: int, k: int) {
  n >= 1 && k >= 2
}

predicate SatisfiesConstraint(x: int, n: int, k: int) {
  x > 0 && k > 0 && (x / k) * (x % k) == n
}

method solve(n: int, k: int) returns (result: int)
  requires ValidInput(n, k)
  ensures result > 0
  ensures SatisfiesConstraint(result, n, k)
  ensures forall x :: x > 0 && (x / k) * (x % k) == n ==> result <= x
{
  result := n * k + 1;
  assert (result / k) * (result % k) == n * 1 == n;
  
  var i := 1;
  while i < k
    invariant 1 <= i <= k
    invariant result > 0
    invariant (result / k) * (result % k) == n
    invariant forall x :: x > 0 && (x / k) * (x % k) == n && x % k < i ==> result <= x
  {
    if n % i == 0 {
      var t := n / i;
      var candidate := t * k + i;
      assert candidate > 0;
      assert candidate / k == t && candidate % k == i;
      assert (candidate / k) * (candidate % k) == t * i == n;
      
      if candidate < result {
        result := candidate;
      }
    }
    i := i + 1;
  }
  
  assert forall r :: 0 <= r < k ==> (forall x :: x > 0 && (x / k) * (x % k) == n && x % k == r ==> result <= x);
}
