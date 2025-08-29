// <vc-helpers>
lemma digits_sum_properties(x: int)
  ensures x >= 0 ==> digits_sum(x) >= 0
  ensures x < 0 ==> digits_sum(x) <= 0
  decreases abs(x)
{
  if abs(x) < 10 {
    // Base case: single digit
  } else {
    // Inductive case
    digits_sum_properties(x / 10);
  }
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def count_nums(arr: List[int]) -> int
Write a function count_nums which takes an array of integers and returns the number of elements which has a sum of digits > 0. If a number is negative, then its first signed digit will be negative: e.g. -123 has signed digits -1, 2, and 3.
*/
// </vc-description>

// <vc-spec>
method count_nums(arr: seq<int>) returns (count: int)
  ensures count >= 0
  ensures count <= |arr|
  ensures count == |set i | 0 <= i < |arr| && digits_sum(arr[i]) > 0|
// </vc-spec>
// <vc-code>
{
  count := 0;
  var i := 0;
  while i < |arr|
    invariant 0 <= i <= |arr|
    invariant count >= 0
    invariant count == |set j | 0 <= j < i && digits_sum(arr[j]) > 0|
  {
    digits_sum_properties(arr[i]);
    if digits_sum(arr[i]) > 0 {
      count := count + 1;
    }
    i := i + 1;
  }
}
// </vc-code>

function digits_sum(x: int): int
  decreases abs(x)
{
  if abs(x) < 10 then x else x % 10 + digits_sum(x / 10)
}
// pure-end
function abs(x: int): int
  ensures abs(x) >= 0
  ensures abs(x) == x || abs(x) == -x
{
  if x >= 0 then x else -x
}
// pure-end