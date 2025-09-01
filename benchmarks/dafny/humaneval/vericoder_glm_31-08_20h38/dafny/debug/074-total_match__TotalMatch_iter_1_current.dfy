function sum_chars_rec(list: seq<string>): nat
{
  if |list| == 0 then 0
  else |list[0]| + sum_chars_rec(list[1..])
}

// <vc-helpers>
method SumChars(list: seq<string>) returns (sum: nat)
  ensures sum == sum_chars_rec(list)
{
  var total := 0;
  var i := 0;
  while i < |list|
    invariant 0 <= i <= |list|
    invariant total == sum_chars_rec(list[0..i])
  {
    total := total + |list[i]|;
    i := i + 1;
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
var c1 := SumChars(list1);
var c2 := SumChars(list2);
if c1 <= c2
// </vc-code>

method SumChars(list: seq<string>) returns (sum: nat)
  // post-conditions-start
  ensures sum == sum_chars_rec(list)
  // post-conditions-end
{
  assume{:axiom} false;
}