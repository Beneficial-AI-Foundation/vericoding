function sum_chars_rec(list: seq<string>): nat
{
  if |list| == 0 then 0
  else |list[0]| + sum_chars_rec(list[1..])
}

// <vc-helpers>
// </vc-helpers>

// <vc-description>
/*
function_signature: method TotalMatch(list1: seq<string>, list2: seq<string>) returns (result: seq<string>)
Process input. Ensures: returns the correct size/count; returns the correct size/count; the result is at most the specified value; the result is at most the specified value; returns the correct value.
*/
// </vc-description>

// <vc-spec>
method TotalMatch(list1: seq<string>, list2: seq<string>) returns (result: seq<string>)
  ensures result == list1 || result == list2
  ensures sum_chars_rec(result) <= sum_chars_rec(list1)
  ensures sum_chars_rec(result) <= sum_chars_rec(list2)
  ensures sum_chars_rec(result) == if sum_chars_rec(list1) <= sum_chars_rec(list2) then sum_chars_rec(list1) else sum_chars_rec(list2)
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