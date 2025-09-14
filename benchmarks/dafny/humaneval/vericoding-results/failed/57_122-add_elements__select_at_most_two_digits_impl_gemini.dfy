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
lemma ConcatLemma(s1: seq<int>, s2: seq<int>)
  requires |s1| + |s2| <= 100
  ensures select_at_most_two_digits_rec(s1 + s2) == select_at_most_two_digits_rec(s1) + select_at_most_two_digits_rec(s2)
  decreases |s1|
{
  if |s1| > 0 {
    ConcatLemma(s1[1..], s2);
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
{
  result := [];
  var i: nat := 0;
  while i < |arr|
    invariant 0 <= i <= |arr|
    invariant result == select_at_most_two_digits_rec(arr[..i])
    decreases |arr| - i
  {
    ConcatLemma(arr[..i], [arr[i]]);
    if 0 <= arr[i] < 100 {
      result := result + [arr[i]];
    }
    i := i + 1;
  }
}
// </vc-code>
