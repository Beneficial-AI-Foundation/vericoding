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
lemma sum_chars_rec_step(list: seq<string>, i: nat)
  requires 0 <= i < |list|
  ensures sum_chars_rec(list[..i+1]) == sum_chars_rec(list[..i]) + |list[i]|
{
  assert list[..i+1] == list[..i] + [list[i]];
  sum_chars_rec_append(list[..i], [list[i]]);
}

lemma sum_chars_rec_append(a: seq<string>, b: seq<string>)
  ensures sum_chars_rec(a + b) == sum_chars_rec(a) + sum_chars_rec(b)
{
  if |a| == 0 {
    assert a + b == b;
  } else {
    assert a + b == [a[0]] + (a[1..] + b);
    sum_chars_rec_append(a[1..], b);
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
    sum_chars_rec_step(list, i);
    sum := sum + |list[i]|;
    i := i + 1;
  }
}
// </vc-code>

