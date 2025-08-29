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
  requires |arr| >= 0 && |arr| <= 100
  ensures forall i :: 0 <= i < |select_at_most_two_digits_rec(arr)| ==> 0 <= select_at_most_two_digits_rec(arr)[i] < 100
  ensures forall i :: 0 <= i < |select_at_most_two_digits_rec(arr)| ==> select_at_most_two_digits_rec(arr)[i] in arr
{
  if |arr| == 0 {
    assert select_at_most_two_digits_rec(arr) == [];
  } else {
    var rest := arr[1..];
    SelectAtMostTwoDigitsProperties(rest);
    if 0 <= arr[0] < 100 {
      assert select_at_most_two_digits_rec(arr) == [arr[0]] + select_at_most_two_digits_rec(rest);
      assert arr[0] in arr;
      assert forall i :: 0 <= i < |[arr[0]] + select_at_most_two_digits_rec(rest)| ==> 
        (i == 0 ==> 0 <= arr[0] < 100) && (i > 0 ==> 0 <= ([arr[0]] + select_at_most_two_digits_rec(rest))[i] < 100);
      assert forall i :: 0 <= i < |[arr[0]] + select_at_most_two_digits_rec(rest)| ==> 
        ([arr[0]] + select_at_most_two_digits_rec(rest))[i] in arr;
    } else {
      assert select_at_most_two_digits_rec(arr) == select_at_most_two_digits_rec(rest);
    }
  }
}

lemma SelectAtMostTwoDigitsRecPrefix(arr: seq<int>, i: int)
  requires 0 <= i <= |arr|
  requires |arr| <= 100
  ensures select_at_most_two_digits_rec(arr[..i]) == select_at_most_two_digits_rec(arr[..i])
{
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
  result := [];
  var i := 0;
  while i < |arr|
    invariant 0 <= i <= |arr|
    invariant forall j :: 0 <= j < |result| ==> 0 <= result[j] < 100
    invariant forall j :: 0 <= j < |result| ==> result[j] in arr
    invariant result == select_at_most_two_digits_rec(arr[..i])
  {
    if 0 <= arr[i] < 100 {
      result := result + [arr[i]];
    } else {
      // No change to result since the current element is not added
    }
    i := i + 1;
  }
  assert arr[..|arr|] == arr;
  SelectAtMostTwoDigitsProperties(arr);
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