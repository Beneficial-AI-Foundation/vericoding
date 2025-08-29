// <vc-helpers>
lemma set_cardinality_lemma(arr: seq<int>, i: int)
  requires 0 <= i < |arr|
  requires digits_sum(arr[i]) > 0
  ensures |set j | 0 <= j < i+1 && digits_sum(arr[j]) > 0| == 
          |set j | 0 <= j < i && digits_sum(arr[j]) > 0| + 1
{
  var old_set := set j | 0 <= j < i && digits_sum(arr[j]) > 0;
  var new_set := set j | 0 <= j < i+1 && digits_sum(arr[j]) > 0;
  
  assert i !in old_set;
  assert new_set == old_set + {i};
}

lemma set_cardinality_lemma_no_change(arr: seq<int>, i: int)
  requires 0 <= i < |arr|
  requires digits_sum(arr[i]) <= 0
  ensures |set j | 0 <= j < i+1 && digits_sum(arr[j]) > 0| == 
          |set j | 0 <= j < i && digits_sum(arr[j]) > 0|
{
  var old_set := set j | 0 <= j < i && digits_sum(arr[j]) > 0;
  var new_set := set j | 0 <= j < i+1 && digits_sum(arr[j]) > 0;
  
  assert new_set == old_set;
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def count_nums(arr: List[int]) -> int
Write a function count_nums which takes an array of integers and returns the number of elements which has a sum of digits > 0. If a number is negative, then its first signed digit will be negative: e.g. -123 has signed digits -1, 2, and 3.
*/
// </vc-description>

// <vc-code>
method count_nums(arr: seq<int>) returns (count: int)
  ensures count >= 0
  ensures count <= |arr|
  ensures count == |set i | 0 <= i < |arr| && digits_sum(arr[i]) > 0|
{
  count := 0;
  var i := 0;
  
  while i < |arr|
    invariant 0 <= i <= |arr|
    invariant count >= 0
    invariant count <= i
    invariant count == |set j | 0 <= j < i && digits_sum(arr[j]) > 0|
  {
    if digits_sum(arr[i]) > 0 {
      set_cardinality_lemma(arr, i);
      count := count + 1;
    } else {
      set_cardinality_lemma_no_change(arr, i);
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