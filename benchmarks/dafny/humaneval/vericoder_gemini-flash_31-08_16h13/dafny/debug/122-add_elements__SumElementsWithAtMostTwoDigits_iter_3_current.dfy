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
function sum_first_k_two_digit_elements(arr: seq<int>, k: int): int
  requires 0 <= k <= |arr|
{
  if k == 0 then 0
  else
    var current_val := arr[k-1];
    var remaining_sum := sum_first_k_two_digit_elements(arr, k-1);
    if 0 <= current_val < 100 then current_val + remaining_sum
    else remaining_sum
}

lemma SumElementsWithAtMostTwoDigits_lemma(arr: seq<int>, k: int)
  requires 0 <= k <= |arr|
  requires |arr| <= 100 // Added to satisfy precondition of `select_at_most_two_digits_rec`
  ensures var two_digits := select_at_most_two_digits_rec(arr[..k]);
          sum(two_digits) == sum_first_k_two_digit_elements(arr, k)
  decreases k
{
  if k == 0 {
    // Base case for k = 0
    var two_digits := select_at_most_two_digits_rec(arr[..0]);
    assert two_digits == [];
    assert sum(two_digits) == 0;
    assert sum_first_k_two_digit_elements(arr, 0) == 0;
  } else {
    SumElementsWithAtMostTwoDigits_lemma(arr, k-1);
    var two_digits_k := select_at_most_two_digits_rec(arr[..k]);
    var two_digits_k_minus_1 := select_at_most_two_digits_rec(arr[..k-1]);

    if 0 <= arr[k-1] < 100 {
      assert two_digits_k == two_digits_k_minus_1 + [arr[k-1]];
      assert sum(two_digits_k) == sum(two_digits_k_minus_1) + arr[k-1];
      assert sum_first_k_two_digit_elements(arr, k) == sum_first_k_two_digit_elements(arr, k-1) + arr[k-1];
    } else {
      assert two_digits_k == two_digits_k_minus_1;
      assert sum(two_digits_k) == sum(two_digits_k_minus_1);
      assert sum_first_k_two_digit_elements(arr, k) == sum_first_k_two_digit_elements(arr, k-1);
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
    invariant |arr| <= 100 // Added to satisfy precondition of `SumElementsWithAtMostTwoDigits_lemma`
    invariant current_sum == sum_first_k_two_digit_elements(arr, i)
  {
    if 0 <= arr[i] < 100 {
      current_sum := current_sum + arr[i];
    }
    i := i + 1;
  }
  s := current_sum;
  SumElementsWithAtMostTwoDigits_lemma(arr, k);
}
// </vc-code>

