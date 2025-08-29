function popcount(n: nat): nat {
  if n == 0 then 0
  else popcount(n / 2) + n % 2
}

// <vc-helpers>
predicate sorted_by_popcount_then_value(arr: seq<nat>)
{
  forall i, j :: 0 <= i < j < |arr| ==>
    (popcount(arr[i]) < popcount(arr[j])) ||
    (popcount(arr[i]) == popcount(arr[j]) && arr[i] <= arr[j])
}

lemma popcount_properties(n: nat)
  ensures popcount(n) >= 0
{
}

predicate should_swap(a: nat, b: nat)
{
  (popcount(a) > popcount(b)) ||
  (popcount(a) == popcount(b) && a > b)
}

lemma swap_maintains_multiset(s: seq<nat>, i: int, j: int)
  requires 0 <= i < |s|
  requires 0 <= j < |s|
  ensures multiset(s[i := s[j]][j := s[i]]) == multiset(s)
{
}

lemma should_swap_correct(a: nat, b: nat)
  ensures should_swap(a, b) <==> 
    (popcount(a) > popcount(b) || (popcount(a) == popcount(b) && a > b))
{
}

lemma sorted_prefix_preserved(arr: seq<nat>, j: int, i: int)
  requires 0 <= j < i < |arr|
  requires forall k, l :: 0 <= k < l < j ==>
    (popcount(arr[k]) < popcount(arr[l])) ||
    (popcount(arr[k]) == popcount(arr[l]) && arr[k] <= arr[l])
  requires should_swap(arr[j], arr[j+1])
  ensures forall k, l :: 0 <= k < l < j ==>
    (popcount(arr[j := arr[j+1]][j+1 := arr[j]][k]) < popcount(arr[j := arr[j+1]][j+1 := arr[j]][l])) ||
    (popcount(arr[j := arr[j+1]][j+1 := arr[j]][k]) == popcount(arr[j := arr[j+1]][j+1 := arr[j]][l]) && 
     arr[j := arr[j+1]][j+1 := arr[j]][k] <= arr[j := arr[j+1]][j+1 := arr[j]][l])
{
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def max_fill_count(grid : list[list[int]], capacity : int) -> int
Please write a function that sorts an array of non-negative integers according to number of ones in their binary representation in ascending order. For similar number of ones, sort based on decimal value.
*/
// </vc-description>

// <vc-spec>
method sort_array(arr: seq<nat>) returns (result: seq<nat>)
  ensures |result| == |arr|
  ensures multiset(result) == multiset(arr)
  ensures sorted_by_popcount_then_value(result)
// </vc-spec>
// <vc-code>
{
  result := arr;
  
  var i := 1;
  while i < |result|
    invariant 1 <= i <= |result|
    invariant |result| == |arr|
    invariant multiset(result) == multiset(arr)
    invariant forall k, l :: 0 <= k < l < i ==>
      (popcount(result[k]) < popcount(result[l])) ||
      (popcount(result[k]) == popcount(result[l]) && result[k] <= result[l])
  {
    var j := i;
    while j > 0 && should_swap(result[j-1], result[j])
      invariant 0 <= j <= i
      invariant |result| == |arr|
      invariant multiset(result) == multiset(arr)
      invariant forall k, l :: 0 <= k < l < j ==>
        (popcount(result[k]) < popcount(result[l])) ||
        (popcount(result[k]) == popcount(result[l]) && result[k] <= result[l])
      invariant forall k, l :: j < k < l <= i ==>
        (popcount(result[k]) < popcount(result[l])) ||
        (popcount(result[k]) == popcount(result[l]) && result[k] <= result[l])
      invariant j < i ==> (forall k :: 0 <= k < j ==> 
        (popcount(result[k]) < popcount(result[j])) ||
        (popcount(result[k]) == popcount(result[j]) && result[k] <= result[j]))
      invariant j < i ==> (forall k :: j < k <= i ==>
        (popcount(result[j]) < popcount(result[k])) ||
        (popcount(result[j]) == popcount(result[k]) && result[j] <= result[k]))
    {
      swap_maintains_multiset(result, j-1, j);
      result := result[j-1 := result[j]][j := result[j-1]];
      j := j - 1;
    }
    i := i + 1;
  }
}
// </vc-code>
