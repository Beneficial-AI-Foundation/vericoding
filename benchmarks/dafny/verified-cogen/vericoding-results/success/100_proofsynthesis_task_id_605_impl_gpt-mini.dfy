// <vc-preamble>
predicate IsDivisible(n: int, divisor: int)
    requires divisor != 0
{
    (n % divisor) == 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): equate modulo with IsDivisible predicate */
lemma ModEquivIsDivisible(n: int, d: int)
  requires d != 0
  ensures (n % d == 0) == IsDivisible(n, d)
{
  if n % d == 0 {
    assert IsDivisible(n, d);
  } else {
    assert !IsDivisible(n, d);
  }
}

// </vc-helpers>

// <vc-spec>
method PrimeNum(n: int) returns (result: bool)
    requires n >= 2
    ensures result == (forall k :: 2 <= k < n ==> !IsDivisible(n, k))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): preserve invariant by using oldk witness when divisor found */
  var k := 2;
  var found := false;
  while k < n
    invariant 2 <= k <= n
    invariant (found <==> exists j :: 2 <= j < k && IsDivisible(n, j))
    decreases n - k
  {
    if n % k == 0 {
      var oldk := k;
      found := true;
      k := n;
      // provide witness oldk for the existential in the invariant
      assert 2 <= oldk;
      assert oldk < k;
      ModEquivIsDivisible(n, oldk);
      assert IsDivisible(n, oldk);
    } else {
      k := k + 1;
    }
  }
  result := !found;
}

// </vc-code>
