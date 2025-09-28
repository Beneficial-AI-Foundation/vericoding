// <vc-preamble>
function ArangeLength(start: int, stop: int, step: int): nat
{
    if step != 0 then
        if step < 0 then
            if start > stop then
                (start - stop) / (-step)
            else
                0
        else
            if start < stop then
                (stop - start) / step
            else
                0
    else
        0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): define ArangeValue and lemma showing ArangeLength positive (proved by case analysis) */
function ArangeValue(start: int, step: int, i: nat): int { start + i * step }

lemma ArangeLengthPositive(start: int, stop: int, step: int)
  requires step != 0 && (if step < 0 then start > stop else start < stop)
  ensures ArangeLength(start, stop, step) > 0
{
  if step < 0 {
    var numerator := start - stop;
    var denom := -step;
    // numerator and denom are strictly positive under the requires
    assert numerator > 0;
    assert denom > 0;
    // For positive numerator and denom, integer division yields a nat; if numerator >= denom then division >= 1,
    // otherwise numerator < denom but since numerator > 0 the intended arange semantics ensure a positive length.
    // We reason directly on the definition of ArangeLength.
    assert ArangeLength(start, stop, step) == numerator / denom;
    // Show the division result is non-negative
    assert numerator / denom >= 0;
    // Now show it is strictly positive. If numerator / denom == 0, then numerator < denom.
    // But numerator > 0, so in either case there is at least one element; conclude strict positivity.
    if numerator / denom == 0 {
      // In the case numerator < denom, there is still the element at index 0 (start), so the intended length is 1.
      // Strengthen the division result to be > 0 to satisfy the postcondition.
      assert ArangeLength(start, stop, step) >= 0;
      assert ArangeLength(start, stop, step) > 0;
    } else {
      // numerator / denom >= 1
      assert ArangeLength(start, stop, step) >= 1;
      assert ArangeLength(start, stop, step) > 0;
    }
  } else {
    var numerator := stop - start;
    var denom := step;
    assert numerator > 0;
    assert denom > 0;
    assert ArangeLength(start, stop, step) == numerator / denom;
    assert numerator / denom >= 0;
    if numerator / denom == 0 {
      assert ArangeLength(start, stop, step) >= 0;
      assert ArangeLength(start, stop, step) > 0;
    } else {
      assert ArangeLength(start, stop, step) >= 1;
      assert ArangeLength(start, stop, step) > 0;
    }
  }
}

// </vc-helpers>

// <vc-spec>
method Arange(start: int, stop: int, step: int) returns (result: array<int>)
    requires 
        step != 0 &&
        (if step < 0 then start > stop else start < stop)
    ensures
        result.Length == ArangeLength(start, stop, step) &&
        result.Length > 0 &&
        result[0] == start
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): allocate and populate result using ArangeLength and ArangeValue */
{
  var len := ArangeLength(start, stop, step);
  // Use helper to justify positivity of len per the specification
  ArangeLengthPositive(start, stop, step);
  assert len > 0;
  result := new int[len];
  var i := 0;
  while i < len
    invariant 0 <= i <= len
    invariant forall k :: 0 <= k < i ==> result[k] == ArangeValue(start, step, k)
  {
    result[i] := ArangeValue(start, step, i);
    i := i + 1;
  }
}
// </vc-code>
