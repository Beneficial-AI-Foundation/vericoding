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

lemma SumCharsRecPrefix(list: seq<string>, i: nat)
  requires 0 <= i <= |list|
  ensures sum_chars_rec(list[..i]) == sum_chars_rec(list[..i])
{
}

lemma SumCharsRecAppend(list: seq<string>, i: nat)
  requires 0 <= i < |list|
  ensures sum_chars_rec(list[..i+1]) == sum_chars_rec(list[..i]) + |list[i]|
{
  if i == 0 {
    assert list[..1] == [list[0]];
    assert sum_chars_rec(list[..1]) == |list[0]|;
    assert sum_chars_rec(list[..0]) == 0;
  } else {
    assert list[..i+1] == list[..i] + [list[i]];
    calc {
      sum_chars_rec(list[..i+1]);
      == |list[0]| + sum_chars_rec(list[1..i+1]);
      == |list[0]| + sum_chars_rec(list[1..i] + [list[i]]);
      == |list[0]| + |list[i]| + sum_chars_rec(list[1..i]);
      == |list[i]| + (|list[0]| + sum_chars_rec(list[1..i]));
      == |list[i]| + sum_chars_rec(list[..i]);
    }
  }
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
    invariant 0 <= i <= |list|
    invariant sum == sum_chars_rec(list[..i])
  {
    sum := sum + |list[i]|;
    i := i + 1;
    SumCharsRecAppend(list, i-1);
  }
}
// </vc-code>
