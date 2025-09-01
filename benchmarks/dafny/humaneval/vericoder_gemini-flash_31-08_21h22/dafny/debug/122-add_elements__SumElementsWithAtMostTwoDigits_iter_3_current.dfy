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
function sum'(s: seq<int>) : int {
  if |s| == 0 then 0 else s[0] + sum'(s[1..])
}

lemma SumOfSelectedElements(arr: seq<int>, k: int)
  requires 0 <= k <= |arr|
  ensures sum(select_at_most_two_digits_rec(arr[..k])) == sum'(select_at_most_two_digits_rec(arr[..k]))
{
  // The two sum functions are identical, which can be proven by induction.
  // The lemma acts as an identity proof for the purpose of verification.
  if k > 0 {
    var s_prime_recursive_call := select_at_most_two_digits_rec(arr[1..k]);
    var s_recursive_call := select_at_most_two_digits_rec(arr[1..k]);
    if 0 <= arr[0] < 100 {
      SumOfSelectedElements(arr[1..], k - 1);
      assert sum(select_at_most_two_digits_rec(arr[..k])) == arr[0] + sum(select_at_most_two_digits_rec(arr[1..k]));
      assert sum'(select_at_most_two_digits_rec(arr[..k])) == arr[0] + sum'(select_at_most_two_digits_rec(arr[1..k]));
      assert sum(s_recursive_call) == sum'(s_prime_recursive_call);
    } else {
      SumOfSelectedElements(arr[1..], k - 1);
      assert sum(select_at_most_two_digits_rec(arr[..k])) == sum(select_at_most_two_digits_rec(arr[1..k]));
      assert sum'(select_at_most_two_digits_rec(arr[..k])) == sum'(select_at_most_two_digits_rec(arr[1..k]));
      assert sum(s_recursive_call) == sum'(s_prime_recursive_call);
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
  // The local variable name 's' conflicts with the return variable 's'.
  // Renaming the local variable to 'current_sum' to avoid the conflict.
  var current_sum := 0;
  var i := 0;
  while i < k
    invariant 0 <= i <= k
    invariant current_sum == sum(select_at_most_two_digits_rec(arr[..i]))
    decreases k - i
  {
    if 0 <= arr[i] < 100 {
      current_sum := current_sum + arr[i];
    }
    i := i + 1;
  }
  return current_sum;
}
// </vc-code>

