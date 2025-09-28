// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
lemma SquareNonNegative(r: real)
  ensures r*r >= 0.0
{
  if r >= 0.0 {
    assert r*r >= 0.0;
  } else {
    var s := -r;
    assert s > 0.0;
    assert r == -s;
    assert r*r == (-s)*(-s);
    assert (-s)*(-s) == s*s;
    assert s*s >= 0.0;
  }
}
// </vc-helpers>

// <vc-spec>
method NumpySquare(x: array<real>) returns (result: array<real>)
  // The result array has the same length as the input
  ensures result.Length == x.Length
  // Each element in result is the square of the corresponding element in x
  ensures forall i :: 0 <= i < x.Length ==> result[i] == x[i] * x[i]
  // All result elements are non-negative (follows from squaring property)
  ensures forall i :: 0 <= i < result.Length ==> result[i] >= 0.0
  // Preserves zeros: if input element is zero, result element is zero
  ensures forall i :: 0 <= i < x.Length && x[i] == 0.0 ==> result[i] == 0.0
// </vc-spec>
// <vc-code>
{
  var n := x.Length;
  result := new real[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant result.Length == n
    invariant n == x.Length
    invariant forall j :: 0 <= j < i ==> result[j] == x[j] * x[j]
    decreases n - i
  {
    result[i] := x[i] * x[i];
    i := i + 1;
  }
  forall j | 0 <= j < result.Length
    ensures result[j] >= 0.0
  {
    assert result.Length == n;
    assert n == x.Length;
    assert j < x.Length;
    assert result[j] == x[j] * x[j];
    SquareNonNegative(x[j]);
    assert result[j] >= 0.0;
  }
}
// </vc-code>
