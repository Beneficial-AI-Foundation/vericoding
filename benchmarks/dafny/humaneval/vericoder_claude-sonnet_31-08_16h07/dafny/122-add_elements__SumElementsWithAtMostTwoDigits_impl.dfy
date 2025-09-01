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
method select_at_most_two_digits(arr: seq<int>) returns (result: seq<int>)
  // pre-conditions-start
  requires |arr| > 0 && |arr| <= 100
  // pre-conditions-end
  // post-conditions-start
  ensures forall i :: 0 <= i < |result| ==> 0 <= result[i] < 100
  ensures forall i :: 0 <= i < |result| ==> result[i] in arr
  ensures result == select_at_most_two_digits_rec(arr)
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma select_at_most_two_digits_correctness(arr: seq<int>)
  requires |arr| >= 0 && |arr| <= 100
  ensures var result := select_at_most_two_digits_rec(arr);
          forall i :: 0 <= i < |result| ==> 0 <= result[i] < 100
  ensures var result := select_at_most_two_digits_rec(arr);
          forall i :: 0 <= i < |result| ==> result[i] in arr
{
  if |arr| == 0 {
    // base case
  } else {
    select_at_most_two_digits_correctness(arr[1..]);
    var tail_result := select_at_most_two_digits_rec(arr[1..]);
    if 0 <= arr[0] < 100 {
      var result := [arr[0]] + tail_result;
      assert result == select_at_most_two_digits_rec(arr);
    } else {
      assert tail_result == select_at_most_two_digits_rec(arr);
    }
  }
}

lemma slice_preserves_bounds(arr: seq<int>, k: int)
  requires |arr| > 0 && |arr| <= 100
  requires 1 <= k <= |arr|
  ensures |arr[..k]| >= 0 && |arr[..k]| <= 100
{
  assert |arr[..k]| == k;
}
// </vc-helpers>

// <vc-spec>
method SumElementsWithAtMostTwoDigits(arr: seq<int>, k: int) returns (s: int)
  // pre-conditions-start
  requires |arr| > 0 && |arr| <= 100
  requires 1 <= k <= |arr|
  // pre-conditions-end
  // post-conditions-start
  ensures var two_digits := select_at_most_two_digits_rec(arr[..k]);
          s == sum(two_digits)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  slice_preserves_bounds(arr, k);
  var slice := arr[..k];
  select_at_most_two_digits_correctness(slice);
  var filtered := select_at_most_two_digits_rec(slice);
  s := sum(filtered);
}
// </vc-code>

