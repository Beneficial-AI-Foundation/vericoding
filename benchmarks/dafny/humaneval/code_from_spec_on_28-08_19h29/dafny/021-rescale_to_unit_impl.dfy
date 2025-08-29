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
function Min(s: seq<real>): real
  requires |s| > 0
{
  if |s| == 1 then s[0]
  else if s[0] < Min(s[1..]) then s[0]
  else Min(s[1..])
}

function Max(s: seq<real>): real
  requires |s| > 0
{
  if |s| == 1 then s[0]
  else if s[0] > Max(s[1..]) then s[0]
  else Max(s[1..])
}

lemma MinMaxDifference(s: seq<real>)
  requires |s| >= 2
  ensures Max(s) >= Min(s)
{
  if |s| == 2 {
    if s[0] >= s[1] {
      assert Max(s) == s[0] && Min(s) == s[1];
    } else {
      assert Max(s) == s[1] && Min(s) == s[0];
    }
  } else {
    MinMaxDifference(s[1..]);
  }
}

lemma MinIsInSeq(s: seq<real>)
  requires |s| > 0
  ensures exists i :: 0 <= i < |s| && s[i] == Min(s)
{
  if |s| == 1 {
    assert s[0] == Min(s);
  } else {
    if s[0] < Min(s[1..]) {
      assert s[0] == Min(s);
    } else {
      MinIsInSeq(s[1..]);
      assert exists i :: 0 <= i < |s[1..]| && s[1..][i] == Min(s[1..]);
      assert exists i :: 1 <= i < |s| && s[i] == Min(s);
    }
  }
}

lemma MaxIsInSeq(s: seq<real>)
  requires |s| > 0
  ensures exists i :: 0 <= i < |s| && s[i] == Max(s)
{
  if |s| == 1 {
    assert s[0] == Max(s);
  } else {
    if s[0] > Max(s[1..]) {
      assert s[0] == Max(s);
    } else {
      MaxIsInSeq(s[1..]);
      assert exists i :: 0 <= i < |s[1..]| && s[1..][i] == Max(s[1..]);
      assert exists i :: 1 <= i < |s| && s[i] == Max(s);
    }
  }
}

lemma MinResultIsZero(s: seq<real>, result: seq<real>, min_val: real, scale: real)
  requires |s| >= 2
  requires |result| == |s|
  requires scale > 0.0
  requires forall i :: 0 <= i < |s| ==> result[i] == (s[i] - min_val) * scale
  requires min_val == Min(s)
  ensures Min(result) == 0.0
{
  MinIsInSeq(s);
  var min_idx :| 0 <= min_idx < |s| && s[min_idx] == Min(s);
  assert result[min_idx] == (s[min_idx] - min_val) * scale;
  assert result[min_idx] == 0.0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall k :: 0 <= k < i ==> result[k] >= 0.0
  {
    assert result[i] == (s[i] - min_val) * scale;
    assert s[i] >= min_val by { MinMaxDifference(s); }
    assert result[i] >= 0.0;
    i := i + 1;
  }
  assert forall k :: 0 <= k < |s| ==> result[k] >= 0.0;
  assert Min(result) == 0.0;
}

lemma MaxResultIsOne(s: seq<real>, result: seq<real>, min_val: real, max_val: real, scale: real)
  requires |s| >= 2
  requires |result| == |s|
  requires scale > 0.0
  requires max_val > min_val
  requires forall i :: 0 <= i < |s| ==> result[i] == (s[i] - min_val) * scale
  requires min_val == Min(s)
  requires max_val == Max(s)
  requires scale == 1.0 / (max_val - min_val)
  ensures Max(result) == 1.0
{
  MaxIsInSeq(s);
  var max_idx :| 0 <= max_idx < |s| && s[max_idx] == Max(s);
  assert result[max_idx] == (s[max_idx] - min_val) * scale;
  assert result[max_idx] == (max_val - min_val) * scale;
  assert result[max_idx] == 1.0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall k :: 0 <= k < i ==> result[k] <= 1.0
  {
    assert result[i] == (s[i] - min_val) * scale;
    assert s[i] <= max_val by { MinMaxDifference(s); }
    assert result[i] <= 1.0;
    i := i + 1;
  }
  assert forall k :: 0 <= k < |s| ==> result[k] <= 1.0;
  assert Max(result) == 1.0;
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
  requires Max(numbers) > Min(numbers)
  ensures |result| == |numbers|
  ensures forall i :: 0 <= i < |numbers| ==> result[i] == (numbers[i] - Min(numbers)) / (Max(numbers) - Min(numbers))
  ensures Min(result) == 0.0
  ensures Max(result) == 1.0
// </vc-spec>
// <vc-code>
{
  var min_val := Min(numbers);
  var max_val := Max(numbers);
  assert max_val > min_val by { MinMaxDifference(numbers); }
  var scale := 1.0 / (max_val - min_val);
  var result_seq: seq<real> := [];
  var i := 0;
  while i < |numbers|
    invariant 0 <= i <= |numbers|
    invariant |result_seq| == i
    invariant forall k :: 0 <= k < i ==> result_seq[k] == (numbers[k] - min_val) * scale
  {
    result_seq := result_seq + [(numbers[i] - min_val) * scale];
    i := i + 1;
  }
  result := result_seq;
  assert forall k :: 0 <= k < |numbers| ==> result[k] == (numbers[k] - min_val) * scale;
  MinResultIsZero(numbers, result, min_val, scale);
  MaxResultIsOne(numbers, result, min_val, max_val, scale);
}
// </vc-code>
