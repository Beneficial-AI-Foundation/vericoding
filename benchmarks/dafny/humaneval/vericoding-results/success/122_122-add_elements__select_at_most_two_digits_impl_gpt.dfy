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
predicate IsTwoDigits(x: int) { 0 <= x < 100 }
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
  var res: seq<int> := [];
  var i: int := |arr|;
  while i > 0
    invariant 0 <= i <= |arr|
    invariant res == select_at_most_two_digits_rec(arr[i..])
    invariant forall j :: 0 <= j < |res| ==> 0 <= res[j] < 100
    invariant forall j :: 0 <= j < |res| ==> res[j] in arr
    decreases i
  {
    i := i - 1;
    assert i < |arr|;
    assert arr[i..][0] == arr[i];
    assert arr[i..][1..] == arr[i+1..];
    assert select_at_most_two_digits_rec(arr[i..]) == (if 0 <= arr[i] < 100 then [arr[i]] + select_at_most_two_digits_rec(arr[i+1..]) else select_at_most_two_digits_rec(arr[i+1..]));
    if 0 <= arr[i] < 100 {
      res := [arr[i]] + res;
      assert arr[i] in arr;
    } else {
    }
  }
  result := res;
}
// </vc-code>
