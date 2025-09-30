// <vc-preamble>
predicate IsDivisible(n: int, divisor: int)
    requires divisor != 0
{
    (n % divisor) == 0
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method IsNonPrime(n: int) returns (result: bool)
    requires n >= 2
    ensures result == (exists k :: 2 <= k < n && IsDivisible(n, k))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): fixed loop invariant and postcondition proof */
  var i := 2;
  result := false;
  while i < n
    invariant 2 <= i <= n
    invariant result == (exists k :: 2 <= k < i && IsDivisible(n, k))
    invariant !result ==> forall k :: 2 <= k < i ==> !IsDivisible(n, k)
  {
    if n % i == 0 {
      result := true;
      assert IsDivisible(n, i);
      assert 2 <= i < n;
      assert exists k :: 2 <= k < n && IsDivisible(n, k);
      break;
    }
    i := i + 1;
  }
  assert i == n || result;
  assert result ==> (exists k :: 2 <= k < n && IsDivisible(n, k));
  assert !result ==> i == n;
  assert !result ==> (forall k :: 2 <= k < n ==> !IsDivisible(n, k));
}
// </vc-code>
