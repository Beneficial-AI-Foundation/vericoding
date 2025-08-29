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
function product_signs(s: seq<int>): int
  ensures |s| == 0 ==> product_signs(s) == 1
  ensures |s| > 0 ==> (product_signs(s) == 1 || product_signs(s) == -1 || product_signs(s) == 0)
  ensures (exists i :: 0 <= i < |s| && s[i] == 0) ==> product_signs(s) == 0
{
  if |s| == 0 then 1
  else if s[0] == 0 then 0
  else if s[0] > 0 then product_signs(s[1..])
  else -product_signs(s[1..])
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def prod_signs(arr: List[int]) -> Optional[int]
You are given an array arr of integers and you need to return sum of magnitudes of integers multiplied by product of all signs of each number in the array, represented by 1, -1 or 0. Note: return None for empty arr.
*/
// </vc-description>

// <vc-spec>
method prod_signs(arr: seq<int>) returns (result: int?)
  ensures |arr| == 0 ==> result.None?
  ensures |arr| > 0 ==> result.Some?
  ensures |arr| > 0 ==> result.value == sum_abs(arr) * product_signs(arr)
// </vc-spec>
// <vc-code>
{
  if |arr| == 0 {
    result := None;
  } else {
    var sum := sum_abs(arr);
    var prod := product_signs(arr);
    result := Some(sum * prod);
  }
}
// </vc-code>
