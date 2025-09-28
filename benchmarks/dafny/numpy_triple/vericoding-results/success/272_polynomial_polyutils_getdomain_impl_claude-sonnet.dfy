// <vc-preamble>
// Method to compute the domain (smallest interval) containing all input points
// </vc-preamble>

// <vc-helpers>
function min_seq(x: seq<real>): real
  requires |x| >= 1
  ensures forall i :: 0 <= i < |x| ==> min_seq(x) <= x[i]
  ensures exists i :: 0 <= i < |x| && x[i] == min_seq(x)
{
  if |x| == 1 then x[0]
  else if x[0] <= min_seq(x[1..]) then x[0]
  else min_seq(x[1..])
}

function max_seq(x: seq<real>): real
  requires |x| >= 1
  ensures forall i :: 0 <= i < |x| ==> max_seq(x) >= x[i]
  ensures exists i :: 0 <= i < |x| && x[i] == max_seq(x)
{
  if |x| == 1 then x[0]
  else if x[0] >= max_seq(x[1..]) then x[0]
  else max_seq(x[1..])
}
// </vc-helpers>

// <vc-spec>
method getdomain(x: seq<real>) returns (result: seq<real>)
  // Input must be non-empty
  requires |x| >= 1
  // Output is exactly 2 elements: [min, max]
  ensures |result| == 2
  // The minimum is less than or equal to the maximum
  ensures result[0] <= result[1]
  // Every element in x is within the computed domain
  ensures forall i :: 0 <= i < |x| ==> result[0] <= x[i] <= result[1]
  // The domain bounds are actually achieved by elements in x
  ensures exists i :: 0 <= i < |x| && x[i] == result[0]
  ensures exists j :: 0 <= j < |x| && x[j] == result[1]
// </vc-spec>
// <vc-code>
{
  var min_val := min_seq(x);
  var max_val := max_seq(x);
  result := [min_val, max_val];
}
// </vc-code>
