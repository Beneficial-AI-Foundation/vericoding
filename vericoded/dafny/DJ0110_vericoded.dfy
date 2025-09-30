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
method PrimeNum(n: int) returns (result: bool)
    requires n >= 2
    ensures result == (forall k :: 2 <= k < n ==> !IsDivisible(n, k))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed postcondition verification by ensuring result matches specification at return */
{
  result := true;
  var i := 2;
  while i < n
    invariant 2 <= i <= n
    invariant result <==> (forall k :: 2 <= k < i ==> !IsDivisible(n, k))
  {
    if n % i == 0 {
      result := false;
      assert IsDivisible(n, i);
      assert !(forall k :: 2 <= k < n ==> !IsDivisible(n, k));
      return;
    }
    i := i + 1;
  }
  assert i == n;
  assert result <==> (forall k :: 2 <= k < n ==> !IsDivisible(n, k));
}
// </vc-code>
