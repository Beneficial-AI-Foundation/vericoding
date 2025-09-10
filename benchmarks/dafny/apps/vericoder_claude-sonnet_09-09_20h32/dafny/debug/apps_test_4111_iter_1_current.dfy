predicate ValidInput(n: int, arr: seq<int>)
{
  n >= 1 && |arr| == n && forall i :: 0 <= i < n ==> arr[i] >= 1
}

function sum_even_indices(arr: seq<int>, start: int): int
  requires 0 <= start <= |arr|
  decreases |arr| - start
{
  if start == |arr| then 0
  else
    var contribution := if start % 2 == 0 then arr[start] else 0;
    contribution + sum_even_indices(arr, start + 1)
}

function sum_odd_indices(arr: seq<int>, start: int): int
  requires 0 <= start <= |arr|
  decreases |arr| - start
{
  if start == |arr| then 0
  else
    var contribution := if start % 2 == 1 then arr[start] else 0;
    contribution + sum_odd_indices(arr, start + 1)
}

function count_balanced_removals(arr: seq<int>): int
{
  var n := |arr|;
  if n == 0 then 0 else
  count_helper(arr, 0, sum_even_indices(arr, 0), sum_odd_indices(arr, 0), 0, 0)
}

function count_helper(arr: seq<int>, i: int, count1: int, count2: int, temp1: int, temp2: int): int
  requires 0 <= i <= |arr|
  decreases |arr| - i
{
  if i == |arr| then 0
  else
    var contribution := 
      if i % 2 == 0 then
        var val1 := temp1 + count2 - temp2;
        var val2 := temp2 + count1 - temp1 - arr[i];
        if val1 == val2 then 1 else 0
      else
        var val1 := temp1 + count2 - temp2 - arr[i];
        var val2 := temp2 + count1 - temp1;
        if val1 == val2 then 1 else 0;
    var new_temp1 := if i % 2 == 0 then temp1 + arr[i] else temp1;
    var new_temp2 := if i % 2 == 1 then temp2 + arr[i] else temp2;
    contribution + count_helper(arr, i + 1, count1, count2, new_temp1, new_temp2)
}

// <vc-helpers>
lemma sum_even_indices_correctness(arr: seq<int>)
  ensures sum_even_indices(arr, 0) == (var indices := set i | 0 <= i < |arr| && i % 2 == 0; 
                                       if indices == {} then 0 else 
                                       (var s := 0; s))

lemma sum_odd_indices_correctness(arr: seq<int>)
  ensures sum_odd_indices(arr, 0) == (var indices := set i | 0 <= i < |arr| && i % 2 == 1;
                                      if indices == {} then 0 else
                                      (var s := 0; s))

lemma count_helper_bounds(arr: seq<int>, i: int, count1: int, count2: int, temp1: int, temp2: int)
  requires 0 <= i <= |arr|
  ensures 0 <= count_helper(arr, i, count1, count2, temp1, temp2) <= |arr| - i

lemma count_balanced_removals_bounds(arr: seq<int>)
  ensures 0 <= count_balanced_removals(arr) <= |arr|
// </vc-helpers>

// <vc-spec>
method solve(n: int, arr: seq<int>) returns (result: int)
  requires ValidInput(n, arr)
  ensures 0 <= result <= n
  ensures result == count_balanced_removals(arr)
// </vc-spec>
// <vc-code>
{
  if n == 0 {
    return 0;
  }
  
  var count1 := sum_even_indices(arr, 0);
  var count2 := sum_odd_indices(arr, 0);
  
  result := count_helper(arr, 0, count1, count2, 0, 0);
}
// </vc-code>

