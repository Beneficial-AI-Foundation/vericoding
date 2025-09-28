// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function IsDivisibleBy11Helper(n: int): bool
{
  n % 11 == 0
}

lemma DivisibilityEquivalence(n: int)
  ensures (n % 11 == 0) <==> (exists k: int :: k * 11 == n)
{
  if n % 11 == 0 {
    var q := n / 11;
    assert q * 11 == n;
  } else {
    forall k: int
      ensures k * 11 != n
    {
      if k * 11 == n {
        assert n % 11 == 0;
        assert false;
      }
    }
  }
}
// </vc-helpers>

// <vc-spec>
method IsDivisibleBy11(n: int) returns (result: bool)
    ensures result <==> (exists k: int :: k * 11 == n)
// </vc-spec>
// <vc-code>
{
  result := n % 11 == 0;
  DivisibilityEquivalence(n);
}
// </vc-code>
