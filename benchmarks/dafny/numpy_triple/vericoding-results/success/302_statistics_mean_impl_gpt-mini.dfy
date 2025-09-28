// <vc-preamble>
// Helper function to compute the sum of all elements in a sequence
function Sum(a: seq<real>): real
{
  if |a| == 0 then 0.0
  else a[0] + Sum(a[1..])
}

// Helper function to find the minimum value in a non-empty sequence
function Min(a: seq<real>): real
  requires |a| > 0
{
  if |a| == 1 then a[0]
  else if a[0] <= Min(a[1..]) then a[0]
  else Min(a[1..])
}

// Helper function to find the maximum value in a non-empty sequence
function Max(a: seq<real>): real
  requires |a| > 0
{
  if |a| == 1 then a[0]
  else if a[0] >= Max(a[1..]) then a[0]
  else Max(a[1..])
}

// Helper predicate to check if all elements in a sequence are equal
predicate IsConstant(a: seq<real>)
{
  |a| > 0 && forall i, j :: 0 <= i < |a| && 0 <= j < |a| ==> a[i] == a[j]
}

// Helper predicate to ensure all elements are within min/max bounds
predicate AllElementsBounded(a: seq<real>, min_val: real, max_val: real)
{
  forall i :: 0 <= i < |a| ==> min_val <= a[i] <= max_val
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): prove sum bounds from per-element bounds */
lemma SumBoundsFromBounds(a: seq<real>, min_val: real, max_val: real)
  requires |a| > 0
  requires AllElementsBounded(a, min_val, max_val)
  ensures (|a| as real) * min_val <= Sum(a) <= (|a| as real) * max_val
  decreases |a|
{
  if |a| == 1 {
    // Sum(a) == a[0] and a[0] in [min_val, max_val]
    assert Sum(a) == a[0];
    assert min_val <= a[0] <= max_val;
    // For |a| == 1 this yields the desired inequalities
    assert (|a| as real) * min_val <= Sum(a);
    assert Sum(a) <= (|a| as real) * max_val;
  } else {
    var rest := a[1..];
    assert AllElementsBounded(rest, min_val, max_val);
    SumBoundsFromBounds(rest, min_val, max_val);
    assert Sum(a) == a[0] + Sum(rest);
    // combine bounds on a[0] and Sum(rest)
    assert (|rest| as real) * min_val <= Sum(rest) <= (|rest| as real) * max_val;
    assert min_val <= a[0] <= max_val;
    assert (|a| as real) * min_val == min_val + (|rest| as real) * min_val;
    assert (|a| as real) * max_val == max_val + (|rest| as real) * max_val;
    assert (|a| as real) * min_val <= a[0] + Sum(rest) <= (|a| as real) * max_val;
    assert (|a| as real) * min_val <= Sum(a) <= (|a| as real) * max_val;
  }
}

/* helper modified by LLM (iteration 4): deduce average bounds by using SumBoundsFromBounds */
lemma AvgBoundsGivenBounds(a: seq<real>, min_val: real, max_val: real)
  requires |a| > 0
  requires AllElementsBounded(a, min_val, max_val)
  ensures min_val <= Sum(a) / (|a| as real) <= max_val
  decreases |a|
{
  // Prove bounds on the sum, then divide by positive length
  SumBoundsFromBounds(a, min_val, max_val);
  assert (|a| as real) * min_val <= Sum(a) <= (|a| as real) * max_val;
  assert |a| > 0;
  assert min_val <= Sum(a) / (|a| as real) <= max_val;
}

/* helper modified by LLM (iteration 4): prove all elements are between Min and Max */
lemma ElementsBetweenMinMax(a: seq<real>)
  requires |a| > 0
  ensures AllElementsBounded(a, Min(a), Max(a))
  decreases |a|
{
  if |a| == 1 {
    // trivial: Min(a) == a[0] == Max(a)
  } else {
    var rest := a[1..];
    ElementsBetweenMinMax(rest);

    // Relations between Min/Max of a and of rest
    if a[0] <= Min(rest) {
      assert Min(a) == a[0];
      assert Min(a) <= Min(rest);
    } else {
      assert Min(a) == Min(rest);
      assert Min(a) <= a[0];
    }

    if a[0] >= Max(rest) {
      assert Max(a) == a[0];
      assert Max(a) >= Max(rest);
    } else {
      assert Max(a) == Max(rest);
      assert Max(a) >= a[0];
    }

    // Now prove bounds for every index
    assert forall i :: 0 <= i < |a| ==> Min(a) <= a[i] <= Max(a);
  }
}

/* helper modified by LLM (iteration 4): sum of constant sequence equals n * value */
lemma SumIsNtimesConst(a: seq<real>)
  requires |a| > 0
  requires IsConstant(a)
  ensures Sum(a) == (|a| as real) * a[0]
  decreases |a|
{
  if |a| == 1 {
    // Sum(a) == a[0]
  } else {
    var rest := a[1..];
    // rest is also constant with same value
    assert IsConstant(rest);
    SumIsNtimesConst(rest);
    assert Sum(a) == a[0] + Sum(rest);
    assert Sum(rest) == (|rest| as real) * a[0];
    assert Sum(a) == a[0] + (|rest| as real) * a[0] == (|a| as real) * a[0];
  }
}

// </vc-helpers>

// <vc-spec>
method Mean(a: seq<real>) returns (result: real)
  requires |a| > 0  // Input sequence must be non-empty
  ensures result == Sum(a) / (|a| as real)  // Core property: mean is sum divided by count
  ensures Min(a) <= result <= Max(a)  // Mean is bounded by minimum and maximum values
  ensures IsConstant(a) ==> result == a[0]  // For constant sequences, mean equals the constant value
  ensures AllElementsBounded(a, Min(a), Max(a))  // Verification that min/max bounds hold for all elements
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): implement mean and use lemmas to prove bounds */
  result := Sum(a) / (|a| as real);
  // Establish that every element lies between Min(a) and Max(a)
  ElementsBetweenMinMax(a);
  // Use those per-element bounds to show the mean lies between Min and Max
  AvgBoundsGivenBounds(a, Min(a), Max(a));
  // If the sequence is constant, prove the mean equals the constant value
  if IsConstant(a) {
    SumIsNtimesConst(a);
    assert result == a[0];
  }
}

// </vc-code>
