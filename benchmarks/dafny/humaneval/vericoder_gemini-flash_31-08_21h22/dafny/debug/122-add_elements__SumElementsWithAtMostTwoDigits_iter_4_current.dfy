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
  requires forall j :: 0 <= j < k ==> |arr[..j]| <= 100 // Add this line
  ensures sum(select_at_most_two_digits_rec(arr[..k])) == sum'(select_at_most_two_digits_rec(arr[..k]))
{
  if k > 0 {
    SumOfSelectedElements(arr[1..], k - 1);
    var s_prime_recursive_call := select_at_most_two_digits_rec(arr[1..k]);
    var s_recursive_call := select_at_most_two_digits_rec(arr[1..k]);
    if 0 <= arr[0] < 100 {
      assert |arr[..k-1]| <= 100;
      assert |arr[1..k]| <= 100;
      assert sum(select_at_most_two_digits_rec(arr[..k])) == arr[0] + sum(select_at_most_two_digits_rec(arr[1..k]));
      assert sum'(select_at_most_two_digits_rec(arr[..k])) == arr[0] + sum'(select_at_most_two_digits_rec(arr[1..k]));
      assert sum(s_recursive_call) == sum'(s_prime_recursive_call);
    } else {
      assert |arr[..k-1]| <= 100;
      assert |arr[1..k]| <= 100;
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
  var current_sum := 0;
  var i := 0;
  while i < k
    invariant 0 <= i <= k
    invariant |arr[..i]| <= 100 // Add this line
    invariant current_sum == sum(select_at_most_two_digits_rec(arr[..i]))
    decreases k - i
  {
    if 0 <= arr[i] < 100 {
      current_sum := current_sum + arr[i];
      assert current_sum == sum(select_at_most_two_digits_rec(arr[..i]) + [arr[i]]) by {
        if |select_at_most_two_digits_rec(arr[..i])| == 0 {
          assert sum(select_at_most_two_digits_rec(arr[..i]) + [arr[i]]) == arr[i];
        } else {
          assert sum(select_at_most_two_digits_rec(arr[..i]) + [arr[i]]) == sum(select_at_most_two_digits_rec(arr[..i])) + arr[i];
        }
      }
    }
    i := i + 1;
    if i <= k && 0 <= i {
      assert |arr[..i]| <= |arr|;
      assert |arr[..i]| <= 100; // This should be provable from the invariant and loop condition
    }
    // Prove the loop invariant for the next iteration
    // The main challenge is to prove: current_sum_after_increment == sum(select_at_most_two_digits_rec(arr[..i_after_increment]))
  }
  return current_sum;
}
// </vc-code>

