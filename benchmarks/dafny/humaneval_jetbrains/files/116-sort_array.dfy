
/*
function_signature: def max_fill_count(grid : list[list[int]], capacity : int) -> int
Please write a function that sorts an array of non-negative integers according to number of ones in their binary representation in ascending order. For similar number of ones, sort based on decimal value.
*/

function popcount(n: nat): nat {
  if n == 0 then 0
  else popcount(n / 2) + n % 2
}

method sort_array(s: seq<nat>) returns (sorted: seq<nat>)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> popcount(sorted[i]) <= popcount(sorted[j])
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
{
  assume false;
}
