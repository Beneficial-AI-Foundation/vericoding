// <vc-preamble>
// Method to compute the domain (smallest interval) containing all input points
// </vc-preamble>

// <vc-helpers>
function min_seq(s: seq<real>, i: int): real
  requires 0 <= i < |s|
  decreases i
{
  if i == 0 then s[0]
  else
    var prev := min_seq(s, i-1);
    if s[i] < prev then s[i] else prev
}

function max_seq(s: seq<real>, i: int): real
  requires 0 <= i < |s|
  decreases i
{
  if i == 0 then s[0]
  else
    var prev := max_seq(s, i-1);
    if s[i] > prev then s[i] else prev
}

lemma min_seq_property(s: seq<real>, i: int)
  requires 0 <= i < |s|
  ensures forall k :: 0 <= k <= i ==> min_seq(s, i) <= s[k]
  ensures exists k :: 0 <= k <= i && s[k] == min_seq(s, i)
  decreases i
{
  if i == 0 {
  } else {
    min_seq_property(s, i-1);
  }
}

lemma max_seq_property(s: seq<real>, i: int)
  requires 0 <= i < |s|
  ensures forall k :: 0 <= k <= i ==> max_seq(s, i) >= s[k]
  ensures exists k :: 0 <= k <= i && s[k] == max_seq(s, i)
  decreases i
{
  if i == 0 {
  } else {
    max_seq_property(s, i-1);
  }
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
  var minVal := min_seq(x, |x| - 1);
  var maxVal := max_seq(x, |x| - 1);
  
  min_seq_property(x, |x| - 1);
  max_seq_property(x, |x| - 1);
  
  result := [minVal, maxVal];
}
// </vc-code>
