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
lemma SumTwoDigitsCorrect(arr: seq<int>, k: int)
  requires |arr| > 0 && |arr| <= 100
  requires 1 <= k <= |arr|
  ensures var two_digits := select_at_most_two_digits_rec(arr[..k]);
          sum(two_digits) == sum(select_at_most_two_digits_rec(arr[..k]))
{
  // This lemma is trivially true since the expression is just a variable binding.
}

lemma SumPrefixCorrect(s: seq<int>, i: int)
  requires 0 <= i <= |s|
  ensures sum(s[..i]) == (if i == 0 then 0 else sum(s[..i-1]) + s[i-1])
{
  if i == 0 {
  } else {
    assert s[..i] == s[..i-1] + [s[i-1]];
    calc {
      sum(s[..i]);
      sum(s[..i-1] + [s[i-1]]);
      { reveal sum(); }
      sum(s[..i-1]) + s[i-1];
    }
  }
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
  var two_digits := select_at_most_two_digits(arr[..k]);
  s := 0;
  var i := 0;
  while i < |two_digits|
    invariant 0 <= i <= |two_digits|
    invariant s == sum(two_digits[..i])
  {
    s := s + two_digits[i];
    i := i + 1;
    if i <= |two_digits| {
      SumPrefixCorrect(two_digits, i);
      assert s == sum(two_digits[..i]);
    }
  }
  assert s == sum(two_digits);
}
// </vc-code>
