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
function sum'(s: seq<int>) : int {
  if |s| == 0 then 0 else s[0] + sum'(s[1..])
}
function select_at_most_two_digits_rec'(arr: seq<int>): seq<int>
  requires |arr| >= 0 && |arr| <= 100
  ensures forall i :: 0 <= i < |select_at_most_two_digits_rec'(arr)| ==> 0 <= select_at_most_two_digits_rec'(arr)[i] < 100
  ensures forall i :: 0 <= i < |select_at_most_two_digits_rec'(arr)| ==> select_at_most_two_digits_rec'(arr)[i] in arr
{
  if |arr| == 0 then []
  else if 0 <= arr[0] < 100 then [arr[0]] + select_at_most_two_digits_rec'(arr[1..])
  else select_at_most_two_digits_rec'(arr[1..])
}

predicate IsSubsequence(sub: seq<int>, main: seq<int>)
{
  exists i, j :: 0 <= i <= j <= |main| && sub == main[i..j]
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
  var i: int := 0;

  while i < |arr|
    invariant 0 <= i <= |arr|
    invariant forall j :: 0 <= j < |result_seq| ==> 0 <= result_seq[j] < 100
    invariant forall j :: 0 <= j < |result_seq| ==> result_seq[j] in arr
    invariant result_seq == select_at_most_two_digits_rec(arr[..i])
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