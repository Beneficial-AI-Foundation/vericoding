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
lemma sum_chars_rec_monotonic(list: seq<string>, i: nat)
  requires i <= |list|
  ensures sum_chars_rec(list[..i]) <= sum_chars_rec(list)
{
  if i == 0 {
    assert list[..i] == [];
  } else if i == |list| {
    assert list[..i] == list;
  } else {
    assert list[..i] + list[i..] == list;
    assert sum_chars_rec(list) == sum_chars_rec(list[..i]) + sum_chars_rec(list[i..]);
    assert sum_chars_rec(list[i..]) >= 0;
  }
}

lemma sum_chars_rec_additive(list: seq<string>, i: nat)
  requires i < |list|
  ensures sum_chars_rec(list[..i+1]) == sum_chars_rec(list[..i]) + |list[i]|
{
  if i == 0 {
    assert list[..0] == [];
    assert list[..1] == [list[0]];
    assert sum_chars_rec([list[0]]) == |list[0]| + sum_chars_rec([]);
    assert sum_chars_rec([]) == 0;
  } else {
    assert list[..i+1] == [list[0]] + list[1..][..i];
    assert list[..i] == [list[0]] + list[1..][..i-1];
    sum_chars_rec_additive(list[1..], i-1);
    assert sum_chars_rec(list[1..][..i]) == sum_chars_rec(list[1..][..i-1]) + |list[1..][i-1]|;
    assert list[1..][i-1] == list[i];
  }
}
// </vc-helpers>

// <vc-description>
/*
function_signature: method SumChars(list: seq<string>) returns (sum: nat)
Calculate sum. Ensures: returns the sum of character lengths in all strings.
*/
// </vc-description>

// <vc-spec>
method SumChars(list: seq<string>) returns (sum: nat)
  ensures sum == sum_chars_rec(list)
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
    sum_chars_rec_additive(list, i-1);
  }
  assert list[..i] == list;
}
// </vc-code>
