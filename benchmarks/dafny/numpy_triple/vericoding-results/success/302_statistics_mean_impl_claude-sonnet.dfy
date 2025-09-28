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
/* helper modified by LLM (iteration 4): Fixed SumBounds lemma with detailed inductive proof */
lemma MinMaxBounds(a: seq<real>)
  requires |a| > 0
  ensures forall i :: 0 <= i < |a| ==> Min(a) <= a[i] <= Max(a)
{
  if |a| == 1 {
    // Base case: single element
  } else {
    MinMaxBounds(a[1..]);
  }
}

lemma ConstantSequenceMean(a: seq<real>)
  requires |a| > 0
  requires IsConstant(a)
  ensures Sum(a) == (|a| as real) * a[0]
{
  if |a| == 1 {
    // Base case
  } else {
    assert a[0] == a[1];
    ConstantSequenceMean(a[1..]);
  }
}

lemma SumBounds(a: seq<real>)
  requires |a| > 0
  ensures (|a| as real) * Min(a) <= Sum(a) <= (|a| as real) * Max(a)
{
  MinMaxBounds(a);
  if |a| == 1 {
    assert Sum(a) == a[0];
    assert Min(a) == a[0] == Max(a);
  } else {
    SumBounds(a[1..]);
    assert Sum(a) == a[0] + Sum(a[1..]);
    assert Min(a) <= a[0] <= Max(a);
    assert (|a[1..]| as real) * Min(a[1..]) <= Sum(a[1..]) <= (|a[1..]| as real) * Max(a[1..]);
    
    // Key: establish that Min(a) <= Min(a[1..]) and Max(a[1..]) <= Max(a)
    if Min(a) == a[0] {
      assert Min(a) <= Min(a[1..]);
    } else {
      assert Min(a) == Min(a[1..]);
    }
    
    if Max(a) == a[0] {
      assert Max(a[1..]) <= Max(a);
    } else {
      assert Max(a) == Max(a[1..]);
    }
    
    // Now we can prove the bounds
    assert (|a[1..]| as real) * Min(a) <= (|a[1..]| as real) * Min(a[1..]);
    assert (|a[1..]| as real) * Max(a[1..]) <= (|a[1..]| as real) * Max(a);
    assert (|a[1..]| as real) * Min(a) <= Sum(a[1..]) <= (|a[1..]| as real) * Max(a);
    
    assert Sum(a) >= a[0] + (|a[1..]| as real) * Min(a);
    assert Sum(a) >= Min(a) + (|a[1..]| as real) * Min(a);
    assert Sum(a) >= (|a| as real) * Min(a);
    
    assert Sum(a) <= a[0] + (|a[1..]| as real) * Max(a);
    assert Sum(a) <= Max(a) + (|a[1..]| as real) * Max(a);
    assert Sum(a) <= (|a| as real) * Max(a);
  }
}

lemma MeanBounds(a: seq<real>)
  requires |a| > 0
  ensures Min(a) <= Sum(a) / (|a| as real) <= Max(a)
{
  SumBounds(a);
  var sum := Sum(a);
  var n := |a| as real;
  assert n > 0.0;
  assert n * Min(a) <= sum <= n * Max(a);
  assert Min(a) <= sum / n <= Max(a);
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
  /* code modified by LLM (iteration 4): Added proper lemma calls to establish sum bounds */
  MinMaxBounds(a);
  MeanBounds(a);
  
  if IsConstant(a) {
    ConstantSequenceMean(a);
  }
  
  result := Sum(a) / (|a| as real);
}
// </vc-code>
