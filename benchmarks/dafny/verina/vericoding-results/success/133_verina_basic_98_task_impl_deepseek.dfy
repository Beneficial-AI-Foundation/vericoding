// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function TripleLemma(y: int): bool 
  ensures TripleLemma(y) <==> (y % 3 == 0 <==> y / 3 * 3 == y) { if y % 3 == 0 then y / 3 * 3 == y else y / 3 * 3 != y }
// </vc-helpers>

// <vc-spec>
method Triple(x: int) returns (result: int)
    ensures result / 3 == x
    ensures result / 3 * 3 == result
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Fixed implementation using multiplication */
  result := 3 * x;
  assert result / 3 == x;
  assert result / 3 * 3 == result;
}
// </vc-code>
