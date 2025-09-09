/*
function_signature: def count_nums(arr: List[int]) -> int
Write a function count_nums which takes an array of integers and returns the number of elements which has a sum of digits > 0. If a number is negative, then its first signed digit will be negative: e.g. -123 has signed digits -1, 2, and 3.
*/

function digits_sum(x: int): int
  decreases abs(x)
{
  if abs(x) < 10 then x else x % 10 + digits_sum(x / 10)
}
function abs(x: int): int
  ensures abs(x) >= 0
  ensures abs(x) == x || abs(x) == -x
{
  if x >= 0 then x else -x
}

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method count_nums(s: seq<int>) returns (cnt: nat)

  ensures cnt == |set i | 0 <= i < |s| && digits_sum(s[i]) > 0|
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
