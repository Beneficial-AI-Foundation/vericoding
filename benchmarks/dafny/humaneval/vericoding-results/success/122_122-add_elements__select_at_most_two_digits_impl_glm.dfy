// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): simplified lemma to focus on essential properties */
lemma SelectAtMostTwoDigitsProperties(arr: seq<int>)
  requires |arr| >= 0 && |arr| <= 100
  ensures forall i :: 0 <= i < |select_at_most_two_digits_rec(arr)| ==> 0 <= select_at_most_two_digits_rec(arr)[i] < 100
  ensures forall i :: 0 <= i < |select_at_most_two_digits_rec(arr)| ==> select_at_most_two_digits_rec(arr)[i] in arr
{
  if |arr| == 0 {
    // Base case: empty sequence satisfies properties vacuously
  } else if 0 <= arr[0] < 100 {
    // Inductive case: first element is valid, rest follows by induction
    SelectAtMostTwoDigitsProperties(arr[1..]);
  } else {
    // Inductive case: first element is invalid, rest follows by induction
    SelectAtMostTwoDigitsProperties(arr[1..]);
  }
}
// </vc-helpers>

// <vc-spec>
method select_at_most_two_digits(arr: seq<int>) returns (result: seq<int>)

  requires |arr| > 0 && |arr| <= 100

  ensures forall i :: 0 <= i < |result| ==> 0 <= result[i] < 100
  ensures forall i :: 0 <= i < |result| ==> result[i] in arr
  ensures result == select_at_most_two_digits_rec(arr)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): call recursive function and use lemma to prove postconditions */
{
  result := select_at_most_two_digits_rec(arr);
  SelectAtMostTwoDigitsProperties(arr);
}
// </vc-code>
