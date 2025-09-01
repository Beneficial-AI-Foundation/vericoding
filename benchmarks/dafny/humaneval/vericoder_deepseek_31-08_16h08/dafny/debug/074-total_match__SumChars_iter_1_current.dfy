function sum_chars_rec(list: seq<string>): nat
{
  if |list| == 0 then 0
  else |list[0]| + sum_chars_rec(list[1..])
}
method TotalMatch(list1: seq<string>, list2: seq<string>) returns (result: seq<string>)
  // post-conditions-start
  ensures |result| == |list1| || |result| == |list2|
  ensures result == list1 || result == list2
  ensures sum_chars_rec(result) <= sum_chars_rec(list1)
  ensures sum_chars_rec(result) <= sum_chars_rec(list2)
  ensures sum_chars_rec(list1) == sum_chars_rec(list2) ==> result == list1
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma sum_chars_rec_non_decreasing(list: seq<string>, i: int)
  requires 0 <= i <= |list|
  ensures sum_chars_rec(list[..i]) <= sum_chars_rec(list)
{
  if i < |list| {
    sum_chars_rec_non_decreasing(list, i + 1);
  }
}

lemma sum_chars_rec_append(list1: seq<string>, list2: seq<string>)
  ensures sum_chars_rec(list1 + list2) == sum_chars_rec(list1) + sum_chars_rec(list2)
{
  if |list1| == 0 {
  } else {
    sum_chars_rec_append(list1[1..], list2);
  }
}

lemma sum_chars_rec_equals(list1: seq<string>, list2: seq<string>)
  requires list1 == list2
  ensures sum_chars_rec(list1) == sum_chars_rec(list2)
{
}
// </vc-helpers>

// <vc-spec>
method SumChars(list: seq<string>) returns (sum: nat)
  // post-conditions-start
  ensures sum == sum_chars_rec(list)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  sum := 0;
  var i := 0;
  while i < |list|
    invariant i <= |list|
    invariant sum == sum_chars_rec(list[..i])
  {
    sum := sum + |list[i]|;
    i := i + 1;
  }
}
// </vc-code>

