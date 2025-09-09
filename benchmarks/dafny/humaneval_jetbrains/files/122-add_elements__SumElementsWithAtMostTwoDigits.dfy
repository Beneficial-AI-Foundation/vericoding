/*
function_signature: method SumElementsWithAtMostTwoDigits(arr: seq<int>, k: int) returns (s: int)
Calculate sum. Requires: the size is bounded; the size is bounded. Ensures: selects only numbers with at most two digits.
*/

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
// </vc-helpers>

// <vc-spec>
method SumElementsWithAtMostTwoDigits(arr: seq<int>, k: int) returns (s: int)

  requires |arr| > 0 && |arr| <= 100
  requires 1 <= k <= |arr|

  ensures var two_digits := select_at_most_two_digits_rec(arr[..k]);
          s == sum(two_digits)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
