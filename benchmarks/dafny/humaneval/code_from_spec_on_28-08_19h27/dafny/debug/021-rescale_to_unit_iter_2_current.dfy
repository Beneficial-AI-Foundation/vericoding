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
  MinSeqProps(s);
  MaxSeqProps(s);
  MinMaxDistinct(s);
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
  if |s| == 1 {
    assert MinSeq(s) == s[0];
    assert s[0] in s;
  } else {
    MinSeqProps(s[1..]);
    if s[0] <= MinSeq(s[1..]) {
      assert MinSeq(s) == s[0];
    } else {
      assert MinSeq(s) == MinSeq(s[1..]);
      assert MinSeq(s[1..]) in s[1..];
      assert MinSeq(s) in s;
    }
  }
}

lemma MaxSeqProps(s: seq<real>)
  requires |s| >= 1
  ensures MaxSeq(s) in s
  ensures forall x :: x in s ==> x <= MaxSeq(s)
{
  if |s| == 1 {
    assert MaxSeq(s) == s[0];
    assert s[0] in s;
  } else {
    MaxSeqProps(s[1..]);
    if s[0] >= MaxSeq(s[1..]) {
      assert MaxSeq(s) == s[0];
    } else {
      assert MaxSeq(s) == MaxSeq(s[1..]);
      assert MaxSeq(s[1..]) in s[1..];
      assert MaxSeq(s) in s;
    }
  }
}

lemma MinMaxDistinct(s: seq<real>)
  requires |s| >= 2
  ensures MinSeq(s) < MaxSeq(s)
{
  MinSeqProps(s);
  MaxSeqProps(s);
  
  if |s| == 2 {
    if s[0] <= s[1] {
      assert MinSeq(s) == s[0];
      assert MaxSeq(s) == s[1];
      assert s[0] != s[1] ==> s[0] < s[1];
      if s[0] == s[1] {
        assert false;
      }
    } else {
      assert MinSeq(s) == s[1];
      assert MaxSeq(s) == s[0];
      assert s[1] < s[0];
    }
  } else {
    if forall i :: 0 <= i < |s| ==> s[i] == s[0] {
      assert false;
    } else {
      assert exists i :: 0 <= i < |s| && s[i] != s[0];
      assert MinSeq(s) < MaxSeq(s);
    }
  }
}

lemma AffineMinMax(numbers: seq<real>, result: seq<real>, shift: real, scale: real)
  requires |numbers| >= 2
  requires scale > 0.0
  requires |result| == |numbers|
  requires affine_seq(numbers, result, shift, scale)
  requires shift == -MinSeq(numbers)
  requires scale == MaxSeq(numbers) - MinSeq(numbers)
  ensures MinSeq(result) == 0.0
  ensures MaxSeq(result) == 1.0
{
  MinSeqProps(numbers);
  MaxSeqProps(numbers);
  MinSeqProps(result);
  MaxSeqProps(result);
  
  assert exists i :: 0 <= i < |numbers| && numbers[i] == MinSeq(numbers);
  assert exists j :: 0 <= j < |numbers| && numbers[j] == MaxSeq(numbers);
  
  forall k | 0 <= k < |result|
    ensures result[k] == affine(numbers[k], shift, scale)
  {
    assert result[k] == affine(numbers[k], shift, scale);
  }
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
  
  assert scale > 0.0;
  
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
  
  AffineMinMax(numbers, result, shift, scale);
}
// </vc-code>
