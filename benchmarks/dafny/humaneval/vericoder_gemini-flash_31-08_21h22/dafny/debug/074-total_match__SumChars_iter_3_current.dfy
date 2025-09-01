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
function sum_chars_rec(list: seq<string>): nat
{
  if |list| == 0 then 0
  else |list[0]| + sum_chars_rec(list[1..])
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
  var s: nat := 0;
  var i: nat := 0;
  while i < |list|
    invariant 0 <= i <= |list|
    invariant s == sum_chars_rec(list[0..i])
  {
    s := s + |list[i]|;
    i := i + 1;
  }
  return s;
}
// </vc-code>

