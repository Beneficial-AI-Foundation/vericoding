predicate ValidInput(n: int, r: int)
{
    n >= 1 && r >= 1
}

function ExpectedResult(n: int, r: int): int
    requires ValidInput(n, r)
{
    var k := if r < n - 1 then r else n - 1;
    k * (k + 1) / 2 + (if r >= n then 1 else 0)
}

// <vc-helpers>
// Helpers to prove divisibility
lemma DivisibilityLemma(k: int)
  requires k >= 0
  ensures k * (k + 1) % 2 == 0
{
  // k*(k+1) is always even, as proved by induction or known property
  if k % 2 == 0 {
    assert (k) * (k + 1) % 2 == 0;
  } else {
    assert (k % 2 == 1) ==> ((k * (k + 1)) % 2 == (1 * (even) + parity of k*k which is 1, wait - standard:
    var even := k % 2 == 0;
    if even {
      // k even, k+1 odd, product even
    } else {
      // k odd, k+1 even, product even
    }
    // Actually, always even: if k even, even*odd=even; if k odd, odd*even=even
Whereas I wrote: if k even, k*(k+1) even; else k odd, (k)*(k+1) odd*even=even. Yes.
  }
}
// </vc-helpers>

// <vc-spec>

// </vc-spec>
// <vc-code>
{
  var k := if r < n - 1 then r else n - 1;
  assert k >= 0;
  DivisibilityLemma(k);
  return k * (k + 1) / 2 + (if r >= n then 1 else 0);
}
// </vc-code>

