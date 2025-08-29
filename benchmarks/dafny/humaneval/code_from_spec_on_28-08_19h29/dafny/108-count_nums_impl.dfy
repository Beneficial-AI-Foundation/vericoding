// <vc-helpers>
function digitsSum(x: int): int
  decreases absValue(x)
{
  if absValue(x) < 10 then x else x % 10 + digitsSum(x / 10)
}

function absValue(x: int): int
  ensures absValue(x) >= 0
  ensures absValue(x) == x || absValue(x) == -x
{
  if x >= 0 then x else -x
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def count_nums(arr: List[int]) -> int
Write a function count_nums which takes an array of integers and returns the number of elements which has a sum of digits > 0. If a number is negative, then its first signed digit will be negative: e.g. -123 has signed digits -1, 2, and 3.
*/
// </vc-description>

// <vc-spec>
method count_nums(arr: array<int>) returns (count: int)
  ensures count >= 0
  ensures count <= arr.Length
  ensures count == |set i: int | 0 <= i < arr.Length && digitsSum(arr[i]) > 0|
// </vc-spec>
// <vc-code>
{
  count := 0;
  var i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant count >= 0
    invariant count == |set k: int | 0 <= k < i && digitsSum(arr[k]) > 0|
  {
    if digitsSum(arr[i]) > 0 {
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