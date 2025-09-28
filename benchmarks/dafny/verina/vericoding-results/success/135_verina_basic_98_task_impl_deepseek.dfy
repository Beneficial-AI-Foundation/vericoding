// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
lemma TripleLemma(x: int) ensures 3 * x == 3 * x && (3 * x) / 3 == x && (3 * x) % 3 == 0 {}
// </vc-helpers>

// <vc-spec>
method Triple(x: int) returns (result: int)
    ensures result / 3 == x
    ensures result / 3 * 3 == result
// </vc-spec>
// <vc-code>
{
  result := 3 * x;
}
// </vc-code>
