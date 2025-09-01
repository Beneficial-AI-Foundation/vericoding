function sum(s: seq<int>) : int {
  if |s| == 0 then 0 else s[0] + sum(s[1..])
}
function select_at_most_two_digits_rec(arr: seq<int>): seq<int>
  requires |arr| >= 0 && |arr| <= 100
{
  if |arr| == 0 then []
  else if 0 <= arr[0] < 100 then [arr[0]] + select_at_most_two_digits_rec(arr[1..])
  else select_at_most_two_digits_rec(arr[1..])
}

// <vc-helpers>
function sum_elements(s: seq<int>) : int {
  if |s| == 0 then 0 else s[0] + sum_elements(s[1..])
}
function select_at_most_two_digits_rec_helper(arr: seq<int>): seq<int>
  requires |arr| >= 0 
  ensures forall i :: 0 <= i < |select_at_most_two_digits_rec_helper(arr)| ==> 0 <= select_at_most_two_digits_rec_helper(arr)[i] < 100
  ensures forall i :: 0 <= i < |select_at_most_two_digits_rec_helper(arr)| ==> select_at_most_two_digits_rec_helper(arr)[i] in arr
  ensures select_at_most_two_digits_rec_helper(arr) == select_at_most_two_digits_rec(arr) // Added equality ensures
{
  if |arr| == 0 then []
  else if 0 <= arr[0] < 100 then [arr[0]] + select_at_most_two_digits_rec_helper(arr[1..])
  else select_at_most_two_digits_rec_helper(arr[1..])
}
// </vc-helpers>

// <vc-spec>
method select_at_most_two_digits(arr: seq<int>) returns (result: seq<int>)
  // pre-conditions-start
  requires |arr| > 0 && |arr| <= 100
  // pre-conditions-end
  // post-conditions-start
  ensures forall i :: 0 <= i < |result| ==> 0 <= result[i] < 100
  ensures forall i :: 0 <= i < |result| ==> result[i] in arr
  ensures result == select_at_most_two_digits_rec(arr)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var result_seq: seq<int> := [];
  var i := 0;

  while i < |arr|
    invariant 0 <= i <= |arr|
    invariant forall j :: 0 <= j < |result_seq| ==> 0 <= result_seq[j] < 100
    invariant forall j :: 0 <= j < |result_seq| ==> result_seq[j] in arr
    invariant result_seq == select_at_most_two_digits_rec_helper(arr[..i])
    decreases |arr| - i
  {
    if 0 <= arr[i] < 100 {
      result_seq := result_seq + [arr[i]];
    }
    i := i + 1;
  }
  return result_seq;
}
// </vc-code>

method SumElementsWithAtMostTwoDigits(arr: seq<int>, k: int) returns (s: int)
  // pre-conditions-start
  requires |arr| > 0 && |arr| <= 100
  requires 1 <= k <= |arr|
  // pre-conditions-end
  // post-conditions-start
  ensures var two_digits := select_at_most_two_digits_rec(arr[..k]);
          s == sum(two_digits)
  // post-conditions-end
{
  assume{:axiom} false;
}