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
lemma SelectAtMostTwoDigitsProperties(arr: seq<int>)
  requires 0 <= |arr| <= 100
  ensures forall i :: 0 <= i < |select_at_most_two_digits_rec(arr)| ==> 0 <= select_at_most_two_digits_rec(arr)[i] < 100
  ensures forall i :: 0 <= i < |select_at_most_two_digits_rec(arr)| ==> select_at_most_two_digits_rec(arr)[i] in arr
  decreases |arr|
{
  if |arr| > 0 {
    SelectAtMostTwoDigitsProperties(arr[1..]);
    if 0 <= arr[0] < 100 {
      var tail := select_at_most_two_digits_rec(arr[1..]);
      assert forall i :: 0 <= i < |tail| ==> 0 <= tail[i] < 100;
      assert forall i :: 0 <= i < |tail| ==> tail[i] in arr[1..];
    } else {
      var tail := select_at_most_two_digits_rec(arr[1..]);
      assert forall i :: 0 <= i < |tail| ==> 0 <= tail[i] < 100;
      assert forall i :: 0 <= i < |tail| ==> tail[i] in arr[1..];
    }
  }
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
  SelectAtMostTwoDigitsProperties(arr);
  return select_at_most_two_digits_rec(arr);
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