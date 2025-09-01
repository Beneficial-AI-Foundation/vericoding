function sum_chars_rec(list: seq<string>): nat
{
  if |list| == 0 then 0
  else |list[0]| + sum_chars_rec(list[1..])
}

// <vc-helpers>

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
  if |list1| == |list2| {
    if sum_chars_rec(list1) <= sum_chars_rec(list2) {
      result := list1;
    } else {
      result := list2;
    }
    assert sum_chars_rec(result) <= sum_chars_rec(list1) by {
      if sum_chars_rec(list1) <= sum_chars_rec(list2) {
      } else {
      }
    }
    assert sum_chars_rec(result) <= sum_chars_rec(list2) by {
      if sum_chars_rec(list1) <= sum_chars_rec(list2) {
      } else {
      }
    }
    if sum_chars_rec(list1) == sum_chars_rec(list2) {
      EqualLengthSameSumImpliesEqual(list1, list2);
      result := list1;
    }
  } else {
    if |list1| < |list2| {
      result := list1;
      LengthInequalityImpliesSumInequality(list1, list2);
    } else {
      result := list2;
      LengthInequalityImpliesSumInequality(list2, list1);
    }
    TotalMatchPostConditionsHold(list1, list2, result);
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