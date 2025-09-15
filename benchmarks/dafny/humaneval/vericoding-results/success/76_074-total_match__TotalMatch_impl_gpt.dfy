// <vc-preamble>
function sum_chars_rec(list: seq<string>): nat
{
  if |list| == 0 then 0
  else |list[0]| + sum_chars_rec(list[1..])
}
// </vc-preamble>

// <vc-helpers>
function ChooseBySum(list1: seq<string>, list2: seq<string>): seq<string> { if sum_chars_rec(list1) <= sum_chars_rec(list2) then list1 else list2 }
// </vc-helpers>

// <vc-spec>
method TotalMatch(list1: seq<string>, list2: seq<string>) returns (result: seq<string>)

  ensures |result| == |list1| || |result| == |list2|
  ensures result == list1 || result == list2
  ensures sum_chars_rec(result) <= sum_chars_rec(list1)
  ensures sum_chars_rec(result) <= sum_chars_rec(list2)
  ensures sum_chars_rec(list1) == sum_chars_rec(list2) ==> result == list1
// </vc-spec>
// <vc-code>
{
  if sum_chars_rec(list1) <= sum_chars_rec(list2) {
    result := list1;
  } else {
    result := list2;
  }
}
// </vc-code>
