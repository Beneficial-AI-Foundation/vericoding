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
/* helper modified by LLM (iteration 3): Added lemmas to prove sum bounds for min and max */
/* helper modified by LLM (iteration 2): Lemma for Min being the minimum */
lemma MinIsMin(a: seq<real>)
  requires 0 < |a|
  ensures forall i :: 0 <= i < |a| ==> Min(a) <= a[i]
{
  if |a| == 1 {
  } else {
    MinIsMin(a[1..]);
  }
}

/* helper modified by LLM (iteration 2): Lemma for Max being the maximum */
lemma MaxIsMax(a: seq<real>)
  requires 0 < |a|
  ensures forall i :: 0 <= i < |a| ==> Max(a) >= a[i]
{
  if |a| == 1 {
  } else {
    MaxIsMax(a[1..]);
  }
}

/* helper modified by LLM (iteration 2): Lemma for Sum if constant */
lemma IsConstantSum(a: seq<real>)
  requires 0 < |a|
  ensures IsConstant(a) ==> Sum(a) == a[0] * (|a| as real)
{
  if |a| == 1 {
    if IsConstant(a) {
      assert Sum(a) == a[0];
      assert (|a| as real) == 1.0;
      assert a[0] * (|a| as real) == a[0];
    }
  } else {
    if IsConstant(a) {
      IsConstantSum(a[1..]);
      assert Sum(a) == a[0] + Sum(a[1..]);
      assert Sum(a[1..]) == a[0] * ((|a|-1) as real);
      var len: real := (|a| as real);
      assert a[0] + a[0] * ((|a|-1) as real) == a[0] * (1.0 + ((|a|-1) as real)) == a[0] * len;
    }
  }
}

/* new lemma: Sum lower bound using Min */
lemma SumLowerBound(a: seq<real>)
  requires 0 < |a|
  ensures Sum(a) >= (|a| as real) * Min(a)
{
  if |a| == 1 {
    // trivial: Sum(a) == a[0] >= 1.0 * Min(a)
  } else {
    SumLowerBound(a[1..]);
    var tailSum: real := Sum(a[1..]);
    var tailMin: real := Min(a[1..]);
    assert Sum(a) == a[0] + tailSum;
    assert tailSum >= ((|a|-1) as real) * tailMin;
    var totalMin: real := Min(a);
    if a[0] < tailMin {
      assert totalMin == a[0];
      assert tailMin >= a[0];
      assert tailSum >= ((|a|-1) as real) * a[0];
      assert Sum(a) >= a[0] + ((|a|-1) as real) * a[0] == (|a| as real) * a[0];
    } else {
      assert totalMin == tailMin;
      assert tailSum >= ((|a|-1) as real) * tailMin;
      assert Sum(a) >= a[0] + ((|a|-1) as real) * tailMin >= tailMin + ((|a|-1) as real) * tailMin == (|a| as real) * tailMin;
    }
  }
}

/* new lemma: Sum upper bound using Max */
lemma SumUpperBound(a: seq<real>)
  requires 0 < |a|
  ensures Sum(a) <= (|a| as real) * Max(a)
{
  if |a| == 1 {
    // trivial: Sum(a) == a[0] <= 1.0 * Max(a)
  } else {
    SumUpperBound(a[1..]);
    var tailSum: real := Sum(a[1..]);
    var tailMax: real := Max(a[1..]);
    assert Sum(a) == a[0] + tailSum;
    assert tailSum <= ((|a|-1) as real) * tailMax;
    var totalMax: real := Max(a);
    if a[0] > tailMax {
      assert totalMax == a[0];
      assert tailMax <= a[0];
      assert tailSum <= ((|a|-1) as real) * a[0];
      assert Sum(a) <= a[0] + ((|a|-1) as real) * a[0] == (|a| as real) * a[0];
    } else {
      assert totalMax == tailMax;
      assert tailSum <= ((|a|-1) as real) * tailMax;
      assert Sum(a) <= a[0] + ((|a|-1) as real) * tailMax <= tailMax + ((|a|-1) as real) * tailMax == (|a| as real) * tailMax;
    }
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
/* code modified by LLM (iteration 3): Add calls to lemmas for postcondition verification including sum bounds */
{
  result := Sum(a) / (|a| as real);
  MinIsMin(a);
  MaxIsMax(a);
  IsConstantSum(a);
  SumLowerBound(a);
  SumUpperBound(a);
}
// </vc-code>
