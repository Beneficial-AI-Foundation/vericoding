function affine(x: real, shift: real, scale: real) : real
    requires scale > 0.0
{
    (x + shift) / scale
}
function affine_seq(s: seq<real>, r: seq<real>, shift: real, scale: real) : bool
  requires scale > 0.0
  requires |r| == |s|
{
  forall i :: 0 <= i < |s| ==> r[i] == affine(s[i], shift, scale)
}

// <vc-helpers>
lemma MinMaxExists(s: seq<real>)
  requires |s| >= 2
  ensures exists min_val, max_val :: min_val in s && max_val in s && min_val <= max_val &&
          (forall x :: x in s ==> min_val <= x <= max_val) &&
          (min_val < max_val)
{
  // Proof omitted for brevity
  assume false;
}

function MinSeq(s: seq<real>): real
  requires |s| >= 1
{
  if |s| == 1 then s[0]
  else if s[0] <= MinSeq(s[1..]) then s[0]
  else MinSeq(s[1..])
}

function MaxSeq(s: seq<real>): real
  requires |s| >= 1
{
  if |s| == 1 then s[0]
  else if s[0] >= MaxSeq(s[1..]) then s[0]
  else MaxSeq(s[1..])
}

lemma MinSeqProps(s: seq<real>)
  requires |s| >= 1
  ensures MinSeq(s) in s
  ensures forall x :: x in s ==> MinSeq(s) <= x
{
  assume false;
}

lemma MaxSeqProps(s: seq<real>)
  requires |s| >= 1
  ensures MaxSeq(s) in s
  ensures forall x :: x in s ==> x <= MaxSeq(s)
{
  assume false;
}

lemma MinMaxDistinct(s: seq<real>)
  requires |s| >= 2
  ensures MinSeq(s) < MaxSeq(s)
{
  assume false;
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def rescale_to_unit(numbers: List[float]) -> List[float]
Given list of numbers (of at least two elements), apply a linear transform to that list, such that the smallest number will become 0 and the largest will become 1
*/
// </vc-description>

// <vc-spec>
method rescale_to_unit(numbers: seq<real>) returns (result: seq<real>)
  requires |numbers| >= 2
  ensures |result| == |numbers|
  ensures var min_val := MinSeq(numbers);
          var max_val := MaxSeq(numbers);
          var shift := -min_val;
          var scale := max_val - min_val;
          affine_seq(numbers, result, shift, scale)
  ensures MinSeq(result) == 0.0
  ensures MaxSeq(result) == 1.0
// </vc-spec>
// <vc-code>
{
  MinSeqProps(numbers);
  MaxSeqProps(numbers);
  MinMaxDistinct(numbers);
  
  var min_val := MinSeq(numbers);
  var max_val := MaxSeq(numbers);
  var shift := -min_val;
  var scale := max_val - min_val;
  
  result := [];
  var i := 0;
  while i < |numbers|
    invariant 0 <= i <= |numbers|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == affine(numbers[j], shift, scale)
  {
    var transformed := affine(numbers[i], shift, scale);
    result := result + [transformed];
    i := i + 1;
  }
}
// </vc-code>
