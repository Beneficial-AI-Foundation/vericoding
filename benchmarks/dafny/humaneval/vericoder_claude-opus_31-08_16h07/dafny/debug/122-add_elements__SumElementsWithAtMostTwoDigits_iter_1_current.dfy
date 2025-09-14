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
lemma sum_property(s: seq<int>, i: int)
  requires 0 <= i <= |s|
  ensures sum(s[..i]) + sum(s[i..]) == sum(s)
{
  if i == 0 {
    assert s[..0] == [];
    assert s[0..] == s;
  } else if i == |s| {
    assert s[..|s|] == s;
    assert s[|s|..] == [];
  } else {
    sum_property(s[1..], i - 1);
  }
}

lemma select_property(arr: seq<int>, i: int)
  requires 0 <= i <= |arr| <= 100
  ensures select_at_most_two_digits_rec(arr[..i]) + select_at_most_two_digits_rec(arr[i..]) == 
          select_at_most_two_digits_rec(arr[..i]) + select_at_most_two_digits_rec(arr[i..])
{
  // Trivial lemma for establishing context
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
  var filtered := select_at_most_two_digits(arr[..k]);
  s := 0;
  var i := 0;
  
  while i < |filtered|
    invariant 0 <= i <= |filtered|
    invariant s == sum(filtered[..i])
    invariant filtered == select_at_most_two_digits_rec(arr[..k])
  {
    s := s + filtered[i];
    assert filtered[..i+1] == filtered[..i] + [filtered[i]];
    i := i + 1;
  }
  
  assert filtered[..|filtered|] == filtered;
}
// </vc-code>

