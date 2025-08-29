function sum_chars_rec(list: seq<string>): nat
{
  if |list| == 0 then 0
  else |list[0]| + sum_chars_rec(list[1..])
}

// <vc-helpers>
lemma SumCharsMonotonicity(list1: seq<string>, list2: seq<string>)
  ensures |list1| <= |list2| && (forall i :: 0 <= i < |list1| ==> |list1[i]| <= |list2[i]|) ==> sum_chars_rec(list1) <= sum_chars_rec(list2)
{
  if |list1| == 0 {
    assert sum_chars_rec(list1) == 0;
  } else {
    if |list1| <= |list2| && (forall i :: 0 <= i < |list1| ==> |list1[i]| <= |list2[i]|) {
      assert sum_chars_rec(list1) == |list1[0]| + sum_chars_rec(list1[1..]);
      assert sum_chars_rec(list2) == |list2[0]| + sum_chars_rec(list2[1..]);
      assert |list1[0]| <= |list2[0]|;
      SumCharsMonotonicity(list1[1..], list2[1..]);
      assert sum_chars_rec(list1[1..]) <= sum_chars_rec(list2[1..]);
      assert sum_chars_rec(list1) <= sum_chars_rec(list2);
    }
  }
}
// </vc-helpers>

// <vc-spec>
method TotalMatch(list1: seq<string>, list2: seq<string>) returns (result: seq<string>)
  // post-conditions-start
  ensures |result| == |list1| || |result| == |list2|
  ensures result == list1 || result == list2
  ensures sum_chars_rec(result) <= sum_chars_rec(list1)
  ensures sum_chars_rec(result) <= sum_chars_rec(list2)
  ensures sum_chars_rec(list1) == sum_chars_rec(list2) ==> result == list1
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var sum1 := SumChars(list1);
  var sum2 := SumChars(list2);
  if sum1 <= sum2 {
    result := list1;
  } else {
    result := list2;
  }
}
// </vc-code>

method SumChars(list: seq<string>) returns (sum: nat)
  // post-conditions-start
  ensures sum == sum_chars_rec(list)
  // post-conditions-end
{
  assume{:axiom} false;
}