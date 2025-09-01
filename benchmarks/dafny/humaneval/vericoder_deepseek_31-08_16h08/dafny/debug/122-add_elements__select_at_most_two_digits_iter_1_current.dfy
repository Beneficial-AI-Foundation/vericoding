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
lemma select_at_most_two_digits_rec_prefix(arr: seq<int>, k: nat)
  requires |arr| >= 0 && |arr| <= 100
  requires k <= |arr|
  ensures select_at_most_two_digits_rec(arr[..k]) + select_at_most_two_digits_rec(arr[k..]) ==
          select_at_most_two_digits_rec(arr)
{
  if k == 0 {
    assert arr[..0] == [];
    assert arr[0..] == arr;
  } else if k == |arr| {
    assert arr[..|arr|] == arr;
    assert arr[|arr|..] == [];
  } else {
    select_at_most_two_digits_rec_prefix(arr[1..], k-1);
  }
}

lemma sum_append(s1: seq<int>, s2: seq<int>)
  ensures sum(s1 + s2) == sum(s1) + sum(s2)
{
  if |s1| == 0 {
    assert s1 + s2 == s2;
  } else {
    sum_append(s1[1..], s2);
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
  var i := 0;
  var r: seq<int> := [];
  
  while i < k
    invariant 0 <= i <= k
    invariant forall j :: 0 <= j < |r| ==> 0 <= r[j] < 100
    invariant forall j :: 0 <= j < |r| ==> r[j] in arr
    invariant r == select_at_most_two_digits_rec(arr[..i])
  {
    if 0 <= arr[i] < 100 {
      r := r + [arr[i]];
    }
    i := i + 1;
  }
  
  s := sum(r);
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