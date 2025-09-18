// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
lemma HelperLemma(x: int, y: int) ensures x + y - y == x { }
// </vc-helpers>

// <vc-spec>
method MultipleReturns(x: int, y: int) returns (result: (int, int))
    ensures result.0 == x + y
    ensures result.1 + y == x
// </vc-spec>
// <vc-code>
{
  var diff := x - y;
  result := (x + y, diff);
  assert result.0 == x + y;
  assert result.1 + y == x;
}
// </vc-code>
