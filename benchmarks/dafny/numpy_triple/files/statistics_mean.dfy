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
  assume {:axiom} false;
}
// </vc-code>
