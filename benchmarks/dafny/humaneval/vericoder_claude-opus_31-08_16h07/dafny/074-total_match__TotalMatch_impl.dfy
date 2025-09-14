function sum_chars_rec(list: seq<string>): nat
{
  if |list| == 0 then 0
  else |list[0]| + sum_chars_rec(list[1..])
}

// <vc-helpers>
lemma SumCharsRecAppend(list: seq<string>, s: string)
  ensures sum_chars_rec(list + [s]) == sum_chars_rec(list) + |s|
{
  if |list| == 0 {
    assert list + [s] == [s];
    assert sum_chars_rec([s]) == |s| + sum_chars_rec([]);
    assert sum_chars_rec([]) == 0;
  } else {
    assert (list + [s])[0] == list[0];
    assert (list + [s])[1..] == list[1..] + [s];
    SumCharsRecAppend(list[1..], s);
  }
}

lemma SumCharsRecProperty(list: seq<string>, i: nat)
  requires 0 <= i <= |list|
  ensures sum_chars_rec(list[..i]) + sum_chars_rec(list[i..]) == sum_chars_rec(list)
{
  if i == 0 {
    assert list[..0] == [];
    assert list[0..] == list;
    assert sum_chars_rec([]) == 0;
  } else if i == |list| {
    assert list[..|list|] == list;
    assert list[|list|..] == [];
    assert sum_chars_rec([]) == 0;
  } else {
    assert list == list[..i] + list[i..];
    SumCharsRecConcat(list[..i], list[i..]);
  }
}

lemma SumCharsRecConcat(list1: seq<string>, list2: seq<string>)
  ensures sum_chars_rec(list1 + list2) == sum_chars_rec(list1) + sum_chars_rec(list2)
{
  if |list1| == 0 {
    assert list1 + list2 == list2;
  } else {
    assert (list1 + list2)[0] == list1[0];
    assert (list1 + list2)[1..] == list1[1..] + list2;
    SumCharsRecConcat(list1[1..], list2);
    assert sum_chars_rec(list1 + list2) == |list1[0]| + sum_chars_rec(list1[1..] + list2);
    assert sum_chars_rec(list1) == |list1[0]| + sum_chars_rec(list1[1..]);
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