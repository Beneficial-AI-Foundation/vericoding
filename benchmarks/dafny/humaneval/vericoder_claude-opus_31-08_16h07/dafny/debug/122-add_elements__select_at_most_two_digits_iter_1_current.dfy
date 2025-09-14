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
lemma select_at_most_two_digits_rec_equivalence(arr: seq<int>, result: seq<int>, index: int)
  requires |arr| >= 0 && |arr| <= 100
  requires 0 <= index <= |arr|
  requires result == select_at_most_two_digits_rec(arr[index..])
  ensures select_at_most_two_digits_rec(arr[index..]) == result
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
    invariant result == select_at_most_two_digits_rec(arr[..i])
    invariant forall j :: 0 <= j < |result| ==> 0 <= result[j] < 100
    invariant forall j :: 0 <= j < |result| ==> result[j] in arr[..i]
  {
    if 0 <= arr[i] < 100 {
      assert arr[..i+1] == arr[..i] + [arr[i]];
      assert select_at_most_two_digits_rec(arr[..i+1]) == 
             select_at_most_two_digits_rec(arr[..i] + [arr[i]]);
      
      if |arr[..i]| == 0 {
        assert select_at_most_two_digits_rec([arr[i]]) == [arr[i]];
      } else {
        assert select_at_most_two_digits_rec(arr[..i] + [arr[i]]) ==
               select_at_most_two_digits_rec(arr[..i]) + [arr[i]];
      }
      
      result := result + [arr[i]];
    } else {
      assert arr[..i+1] == arr[..i] + [arr[i]];
      assert select_at_most_two_digits_rec(arr[..i+1]) == 
             select_at_most_two_digits_rec(arr[..i]);
    }
    i := i + 1;
  }
  
  assert arr[..|arr|] == arr;
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