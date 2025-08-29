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
lemma select_at_most_two_digits_properties(arr: seq<int>)
  requires |arr| >= 0 && |arr| <= 100
  ensures forall x :: x in select_at_most_two_digits_rec(arr) ==> 0 <= x < 100
  ensures forall x :: x in select_at_most_two_digits_rec(arr) ==> x in arr
{
  if |arr| == 0 {
  } else {
    select_at_most_two_digits_properties(arr[1..]);
  }
}

lemma select_at_most_two_digits_step_add(arr: seq<int>, i: int)
  requires |arr| >= 0 && |arr| <= 100
  requires 0 <= i < |arr|
  requires 0 <= arr[i] < 100
  ensures select_at_most_two_digits_rec(arr[..i+1]) == select_at_most_two_digits_rec(arr[..i]) + [arr[i]]
{
  if i == 0 {
    assert arr[..1] == [arr[0]];
    assert arr[..0] == [];
  } else {
    var prefix := arr[..i+1];
    var shorter_prefix := arr[..i];
    
    if 0 <= arr[0] < 100 {
      assert select_at_most_two_digits_rec(prefix) == [arr[0]] + select_at_most_two_digits_rec(prefix[1..]);
      assert select_at_most_two_digits_rec(shorter_prefix) == [arr[0]] + select_at_most_two_digits_rec(shorter_prefix[1..]);
      assert prefix[1..] == arr[1..i+1];
      assert shorter_prefix[1..] == arr[1..i];
      select_at_most_two_digits_step_add(arr[1..], i-1);
    } else {
      assert select_at_most_two_digits_rec(prefix) == select_at_most_two_digits_rec(prefix[1..]);
      assert select_at_most_two_digits_rec(shorter_prefix) == select_at_most_two_digits_rec(shorter_prefix[1..]);
      assert prefix[1..] == arr[1..i+1];
      assert shorter_prefix[1..] == arr[1..i];
      select_at_most_two_digits_step_add(arr[1..], i-1);
    }
  }
}

lemma select_at_most_two_digits_step_skip(arr: seq<int>, i: int)
  requires |arr| >= 0 && |arr| <= 100
  requires 0 <= i < |arr|
  requires !(0 <= arr[i] < 100)
  ensures select_at_most_two_digits_rec(arr[..i+1]) == select_at_most_two_digits_rec(arr[..i])
{
  if i == 0 {
    assert arr[..1] == [arr[0]];
    assert arr[..0] == [];
  } else {
    var prefix := arr[..i+1];
    var shorter_prefix := arr[..i];
    
    if 0 <= arr[0] < 100 {
      assert select_at_most_two_digits_rec(prefix) == [arr[0]] + select_at_most_two_digits_rec(prefix[1..]);
      assert select_at_most_two_digits_rec(shorter_prefix) == [arr[0]] + select_at_most_two_digits_rec(shorter_prefix[1..]);
      assert prefix[1..] == arr[1..i+1];
      assert shorter_prefix[1..] == arr[1..i];
      select_at_most_two_digits_step_skip(arr[1..], i-1);
    } else {
      assert select_at_most_two_digits_rec(prefix) == select_at_most_two_digits_rec(prefix[1..]);
      assert select_at_most_two_digits_rec(shorter_prefix) == select_at_most_two_digits_rec(shorter_prefix[1..]);
      assert prefix[1..] == arr[1..i+1];
      assert shorter_prefix[1..] == arr[1..i];
      select_at_most_two_digits_step_skip(arr[1..], i-1);
    }
  }
}
// </vc-helpers>

// <vc-description>
/*
function_signature: method select_at_most_two_digits(arr: seq<int>) returns (result: seq<int>)
Select elements. Requires: the size is bounded. Ensures: the condition holds for all values; the condition holds for all values; selects only numbers with at most two digits.
*/
// </vc-description>

// <vc-spec>
method select_at_most_two_digits(arr: seq<int>) returns (result: seq<int>)
  requires |arr| >= 0 && |arr| <= 100
  ensures forall x :: x in result ==> 0 <= x < 100
  ensures forall x :: x in result ==> x in arr
  ensures result == select_at_most_two_digits_rec(arr)
// </vc-spec>
// <vc-code>
{
  result := [];
  var i := 0;
  
  while i < |arr|
    invariant 0 <= i <= |arr|
    invariant result == select_at_most_two_digits_rec(arr[..i])
    invariant forall x :: x in result ==> 0 <= x < 100
    invariant forall x :: x in result ==> x in arr
  {
    if 0 <= arr[i] < 100 {
      select_at_most_two_digits_step_add(arr, i);
      result := result + [arr[i]];
    } else {
      select_at_most_two_digits_step_skip(arr, i);
    }
    i := i + 1;
  }
  
  assert arr[..i] == arr;
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