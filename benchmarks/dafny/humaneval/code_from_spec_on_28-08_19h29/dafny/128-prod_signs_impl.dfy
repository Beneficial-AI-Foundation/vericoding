function abs(x: int): int
  ensures abs(x) >= 0
  ensures abs(x) == x || abs(x) == -x
  ensures x >= 0 ==> abs(x) == x
  ensures x < 0 ==> abs(x) == -x
{
  if x >= 0 then x else -x
}
function sum_abs(s: seq<int>) : int
  ensures sum_abs(s) >= 0
{
  if |s| == 0 then 0 else abs(s[0]) + sum_abs(s[1..])
}

// <vc-helpers>
function sign(x: int): int
  ensures sign(x) == -1 || sign(x) == 0 || sign(x) == 1
  ensures x > 0 ==> sign(x) == 1
  ensures x < 0 ==> sign(x) == -1
  ensures x == 0 ==> sign(x) == 0
{
  if x > 0 then 1 else if x < 0 then -1 else 0
}

function prod_signs_helper(s: seq<int>, index: int): int
  requires 0 <= index <= |s|
  ensures index == |s| ==> prod_signs_helper(s, index) == 1
  ensures index < |s| ==> prod_signs_helper(s, index) == sign(s[index]) * prod_signs_helper(s, index + 1)
  decreases |s| - index
{
  if index == |s| then 1
  else sign(s[index]) * prod_signs_helper(s, index + 1)
}

function sum_magnitudes(s: seq<int>): int
  ensures sum_magnitudes(s) >= 0
{
  if |s| == 0 then 0 else abs(s[0]) + sum_magnitudes(s[1..])
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def prod_signs(arr: List[int]) -> Optional[int]
You are given an array arr of integers and you need to return sum of magnitudes of integers multiplied by product of all signs of each number in the array, represented by 1, -1 or 0. Note: return None for empty arr.
*/
// </vc-description>

// <vc-spec>
function prod_signs(arr: seq<int>): (result: int)
  ensures |arr| == 0 ==> result == 0
  ensures |arr| > 0 ==> result == sum_magnitudes(arr) * prod_signs_helper(arr, 0)
// </vc-spec>
// <vc-code>
{
  if |arr| == 0 then 0
  else sum_magnitudes(arr) * prod_signs_helper(arr, 0)
}
// </vc-code>
