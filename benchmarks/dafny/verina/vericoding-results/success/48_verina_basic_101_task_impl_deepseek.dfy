// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
lemma TripleLemma(x: int)
  ensures exists r: int :: r == 3 * x && r / 3 == x && r / 3 * 3 == r
{
  var r := 3 * x;
  assert r / 3 == x;
  assert r / 3 * 3 == r;
}
// </vc-helpers>

// <vc-spec>
method triple(x: int) returns (result: int)
    ensures
        result / 3 == x &&
        result / 3 * 3 == result
// </vc-spec>
// <vc-code>
{
  var r: int := 3 * x;
  result := r;
  assert result / 3 == x;
  assert result / 3 * 3 == result;
}
// </vc-code>
