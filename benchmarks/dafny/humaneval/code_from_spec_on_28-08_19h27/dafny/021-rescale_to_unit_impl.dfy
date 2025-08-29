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
  ensures exists min_val, max_val :: (min_val in s && max_val in s && min_val <= max_val &&
          (forall x :: x in s ==> min_val <= x <= max_val) &&
          (min_val < max_val))
{
  MinSeqProps(s);
  MaxSeqProps(s);
  MinMaxDistinct(s);
}

function MinSeq(s: seq<real>): real
  requires |s| >= 1
  ensures MinSeq(s) in s
  ensures forall x :: x in s ==> MinSeq(s) <= x
{
  if |s| == 1 then s[0]
  else if s[0] <= MinSeq(s[1..]) then 
    (assert forall x :: x in s[1..] ==> MinSeq(s[1..]) <= x; s[0])
  else 
    (assert forall x :: x in s[1..] ==> MinSeq(s[1..]) <= x;
     assert s[0] > MinSeq(s[1..]);
     assert forall x :: x in s ==> (x == s[0] || x in s[1..]);
     MinSeq(s[1..]))
}

function MaxSeq(s: seq<real>): real
  requires |s| >= 1
  ensures MaxSeq(s) in s
  ensures forall x :: x in s ==> x <= MaxSeq(s)
{
  if |s| == 1 then s[0]
  else if s[0] >= MaxSeq(s[1..]) then 
    (assert forall x :: x in s[1..] ==> x <= MaxSeq(s[1..]); s[0])
  else 
    (assert forall x :: x in s[1..] ==> x <= MaxSeq(s[1..]);
     assert s[0] < MaxSeq(s[1..]);
     assert forall x :: x in s ==> (x == s[0] || x in s[1..]);
     MaxSeq(s[1..]))
}

lemma MinSeqProps(s: seq<real>)
  requires |s| >= 1
  ensures MinSeq(s) in s
  ensures forall x :: x in s ==> MinSeq(s) <= x
{
  if |s| == 1 {
  } else {
    MinSeqProps(s[1..]);
    if s[0] <= MinSeq(s[1..]) {
      assert s[0] in s;
      forall x | x in s
        ensures s[0] <= x
      {
        if x == s[0] {
        } else {
          assert x in s[1..];
        }
      }
    } else {
      forall x | x in s
        ensures MinSeq(s[1..]) <= x
      {
        if x in s[1..] {
        } else {
          assert x == s[0];
        }
      }
    }
  }
}

lemma MaxSeqProps(s: seq<real>)
  requires |s| >= 1
  ensures MaxSeq(s) in s
  ensures forall x :: x in s ==> x <= MaxSeq(s)
{
  if |s| == 1 {
  } else {
    MaxSeqProps(s[1..]);
    if s[0] >= MaxSeq(s[1..]) {
      assert s[0] in s;
      forall x | x in s
        ensures x <= s[0]
      {
        if x == s[0] {
        } else {
          assert x in s[1..];
        }
      }
    } else {
      forall x | x in s
        ensures x <= MaxSeq(s[1..])
      {
        if x in s[1..] {
        } else {
          assert x == s[0];
        }
      }
    }
  }
}

lemma MinMaxDistinct(s: seq<real>)
  requires |s| >= 2
  ensures MinSeq(s) < MaxSeq(s)
{
  MinSeqProps(s);
  MaxSeqProps(s);
  
  if forall i, j :: 0 <= i < |s| && 0 <= j < |s| ==> s[i] == s[j] {
    assert s[0] == s[1];
    assert MinSeq(s) == s[0];
    assert MaxSeq(s) == s[0];
    assert MinSeq(s) == MaxSeq(s);
    assert false;
  }
  
  assert exists i, j :: 0 <= i < |s| && 0 <= j < |s| && s[i] != s[j];
  var i, j :| 0 <= i < |s| && 0 <= j < |s| && s[i] != s[j];
  
  if s[i] < s[j] {
    assert MinSeq(s) <= s[i] < s[j] <= MaxSeq(s);
  } else {
    assert MinSeq(s) <= s[j] < s[i] <= MaxSeq(s);
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
  
  var min_idx :| 0 <= min_idx < |numbers| && numbers[min_idx] == MinSeq(numbers);
  var max_idx :| 0 <= max_idx < |numbers| && numbers[max_idx] == MaxSeq(numbers);
  
  calc {
    result[min_idx];
    == affine(numbers[min_idx], shift, scale);
    == affine(MinSeq(numbers), -MinSeq(numbers), MaxSeq(numbers) - MinSeq(numbers));
    == (MinSeq(numbers) - MinSeq(numbers)) / (MaxSeq(numbers) - MinSeq(numbers));
    == 0.0 / (MaxSeq(numbers) - MinSeq(numbers));
    == 0.0;
  }
  
  calc {
    result[max_idx];
    == affine(numbers[max_idx], shift, scale);
    == affine(MaxSeq(numbers), -MinSeq(numbers), MaxSeq(numbers) - MinSeq(numbers));
    == (MaxSeq(numbers) - MinSeq(numbers)) / (MaxSeq(numbers) - MinSeq(numbers));
    == 1.0;
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
    invariant scale > 0.0
  {
    var transformed := affine(numbers[i], shift, scale);
    result := result + [transformed];
    i := i + 1;
  }
  
  AffineMinMax(numbers, result, shift, scale);
}
// </vc-code>
