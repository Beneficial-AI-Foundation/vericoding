// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method IsDivisibleBy11(n: int) returns (result: bool)
    ensures result <==> (exists k: int :: k * 11 == n)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): compute divisibility by 11 using modulo operation */
  if n % 11 == 0 {
    result := true;
    assert n / 11 * 11 == n;
    assert exists k: int :: k * 11 == n;
  } else {
    result := false;
    assert n % 11 != 0;
    assert forall k: int :: k * 11 != n;
  }
}
// </vc-code>
