function select_at_most_two_digits_rec(arr: seq<int>): seq<int>
  requires |arr| >= 0 && |arr| <= 100
{
  if |arr| == 0 then []
  else if 0 <= arr[0] < 100 then [arr[0]] + select_at_most_two_digits_rec(arr[1..])
  else select_at_most_two_digits_rec(arr[1..])
}
// pure-end
lemma select_prop(s: seq<int>)
  requires |s| > 0 && |s| <= 100
  ensures select_at_most_two_digits_rec(s) == select_at_most_two_digits_rec(s[..|s| - 1]) + if 0 <= s[|s| - 1] < 100 then [s[|s| - 1]] else []
{
  if (|s| > 1) {
    assert (s[1..][..|s[1..]| - 1]) == s[1..|s| - 1];
  }
}
// pure-end
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
  // impl-start
  result := [];
  var i := 0;
  while i < |arr|
    // invariants-start
    invariant 0 <= i <= |arr|
    invariant forall j :: 0 <= j < |result| ==> result[j] in arr
    invariant forall j :: 0 <= j < |result| ==> 0 <= result[j] < 100
    invariant |result| <= i
    invariant result == select_at_most_two_digits_rec(arr[..i])
    // invariants-end
  {
    if 0 <= arr[i] < 100 {
      result := result + [arr[i]];
    }
    // assert-start
    assert select_at_most_two_digits_rec(arr[..i + 1]) == select_at_most_two_digits_rec(arr[..i]) + if 0 <= arr[i] < 100 then [arr[i]] else [] by {
      assert arr[..i+1][..i] == arr[..i];
      select_prop(arr[..i + 1]);
    }
    // assert-end
    i := i + 1;
  }
  assert arr[..|arr|] == arr; // assert-line
  // impl-end
}

function sum(s: seq<int>) : int {
  if |s| == 0 then 0 else s[0] + sum(s[1..])
}
// pure-end
lemma sum_prop(s: seq<int>)
  requires |s| > 0
  ensures sum(s) == sum(s[..|s| - 1]) + s[ |s| - 1 ]
{
  if (|s| > 1) {
    assert (s[1..][..|s[1..]| - 1]) == s[1..|s| - 1];
  }
}
// pure-end
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
  // impl-start
  var two_digits := select_at_most_two_digits(arr[..k]);
  s := 0;
  var i := 0;
  while i < |two_digits|
    // invariants-start
    invariant 0 <= i <= |two_digits|
    invariant s == sum(two_digits[..i])
    // invariants-end
  {
    s := s + two_digits[i];
    // assert-start
    assert sum(two_digits[..i + 1]) == sum(two_digits[..i]) + two_digits[i] by {
      assert two_digits[..i+1][..i] == two_digits[..i];
      sum_prop(two_digits[..i + 1]);
   }
    // assert-end
    i := i + 1;
  }
  assert two_digits[..|two_digits|] == two_digits; // assert-line
  // impl-end
}
