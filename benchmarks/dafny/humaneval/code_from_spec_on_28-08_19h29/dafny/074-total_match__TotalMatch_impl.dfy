function sum_chars_rec(list: seq<string>): nat
{
  if |list| == 0 then 0
  else |list[0]| + sum_chars_rec(list[1..])
}

// <vc-helpers>
// Helper lemma to prove properties about sum_chars_rec if needed
lemma SumCharsRecNonNegative(list: seq<string>)
  ensures sum_chars_rec(list) >= 0
{
  if |list| == 0 {
    assert sum_chars_rec(list) == 0;
  } else {
    SumCharsRecNonNegative(list[1..]);
    assert sum_chars_rec(list) == |list[0]| + sum_chars_rec(list[1..]);
    assert |list[0]| >= 0;
    assert sum_chars_rec(list[1..]) >= 0;
  }
}
// </vc-helpers>

// <vc-description>
/*
function_signature: method TotalMatch(list1: seq<string>, list2: seq<string>) returns (result: seq<string>)
Process input. Ensures: returns the correct size/count; returns the correct size/count; the result is at most the specified value; the result is at most the specified value; returns the correct value.
*/
// </vc-description>

// <vc-spec>
method TotalMatch(list1: seq<string>, list2: seq<string>) returns (result: seq<string>)
  requires |list1| == |list2|
  ensures |result| == |list1|
  ensures forall i :: 0 <= i < |result| ==> |result[i]| <= |list1[i]| && |result[i]| <= |list2[i]|
  ensures forall i :: 0 <= i < |result| ==> |result[i]| == if |list1[i]| <= |list2[i]| then |list1[i]| else |list2[i]|
// </vc-spec>
// <vc-code>
{
  var res: seq<string> := [];
  for i := 0 to |list1|
    invariant |res| == i
    invariant forall k :: 0 <= k < i ==> |res[k]| <= |list1[k]| && |res[k]| <= |list2[k]|
    invariant forall k :: 0 <= k < i ==> |res[k]| == if |list1[k]| <= |list2[k]| then |list1[k]| else |list2[k]|
  {
    var len := if |list1[i]| <= |list2[i]| then |list1[i]| else |list2[i]|;
    var dummyStr := list1[i][..len];
    res := res + [dummyStr];
  }
  result := res;
}
// </vc-code>

method SumChars(list: seq<string>) returns (sum: nat)
  // post-conditions-start
  ensures sum == sum_chars_rec(list)
  // post-conditions-end
{
  assume{:axiom} false;
}