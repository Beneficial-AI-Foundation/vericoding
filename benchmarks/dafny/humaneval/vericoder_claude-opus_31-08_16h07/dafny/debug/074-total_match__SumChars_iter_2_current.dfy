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
lemma SumCharsRecProperty(list: seq<string>, i: nat)
  requires 0 <= i <= |list|
  ensures sum_chars_rec(list[i..]) == sum_chars_rec(list[i..])
{
  // Trivial lemma for clarity
}

lemma SumCharsRecSplit(list: seq<string>, i: nat)
  requires 0 <= i < |list|
  ensures sum_chars_rec(list[i..]) == |list[i]| + sum_chars_rec(list[i+1..])
{
  assert list[i..][0] == list[i];
  assert list[i..][1..] == list[i+1..];
}

lemma SumCharsRecAppend(list: seq<string>, i: nat)
  requires 0 <= i < |list|
  ensures sum_chars_rec(list[0..i+1]) == sum_chars_rec(list[0..i]) + |list[i]|
{
  if i == 0 {
    assert list[0..1] == [list[0]];
    assert sum_chars_rec([list[0]]) == |list[0]| + sum_chars_rec([]);
    assert sum_chars_rec([]) == 0;
    assert sum_chars_rec(list[0..0]) == 0;
  } else {
    assert list[0..i+1] == list[0..i] + [list[i]];
    var prefix := list[0..i];
    var single := [list[i]];
    assert list[0..i+1] == prefix + single;
    SumCharsRecConcat(prefix, single);
  }
}

lemma SumCharsRecConcat(s1: seq<string>, s2: seq<string>)
  ensures sum_chars_rec(s1 + s2) == sum_chars_rec(s1) + sum_chars_rec(s2)
{
  if |s1| == 0 {
    assert s1 + s2 == s2;
  } else {
    assert (s1 + s2)[0] == s1[0];
    assert (s1 + s2)[1..] == s1[1..] + s2;
    SumCharsRecConcat(s1[1..], s2);
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
    invariant sum == sum_chars_rec(list[0..i])
  {
    SumCharsRecAppend(list, i);
    sum := sum + |list[i]|;
    i := i + 1;
  }
  
  assert i == |list|;
  assert list[0..|list|] == list;
}
// </vc-code>

