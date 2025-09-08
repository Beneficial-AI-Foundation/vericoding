Given n candies with weights, determine how many candies can be given to dad
such that when the remaining n-1 candies are eaten in numerical order (one per day),
the sum of weights eaten on even-numbered days equals the sum on odd-numbered days.

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

method solve(n: int, arr: seq<int>) returns (result: int)
  requires ValidInput(n, arr)
  ensures 0 <= result <= n
  ensures result == count_balanced_removals(arr)
{
  var count1 := 0;
  var count2 := 0;

  for i := 0 to n
    invariant 0 <= i <= n
    invariant count1 == sum_even_indices(arr, 0) - sum_even_indices(arr, i)
    invariant count2 == sum_odd_indices(arr, 0) - sum_odd_indices(arr, i)
  {
    if i % 2 == 0 {
      count1 := count1 + arr[i];
    } else {
      count2 := count2 + arr[i];
    }
  }

  var ans := 0;
  var temp1 := 0;
  var temp2 := 0;

  for i := 0 to n
    invariant 0 <= i <= n
    invariant 0 <= ans <= i
    invariant temp1 == sum_even_indices(arr, 0) - sum_even_indices(arr, i)
    invariant temp2 == sum_odd_indices(arr, 0) - sum_odd_indices(arr, i)
    invariant count1 == sum_even_indices(arr, 0)
    invariant count2 == sum_odd_indices(arr, 0)
    invariant ans == count_helper(arr, 0, count1, count2, 0, 0) - count_helper(arr, i, count1, count2, temp1, temp2)
  {
    if i % 2 == 0 {
      var val1 := temp1 + count2 - temp2;
      var val2 := temp2 + count1 - temp1 - arr[i];
      if val1 == val2 {
        ans := ans + 1;
      }
      temp1 := temp1 + arr[i];
    } else {
      var val1 := temp1 + count2 - temp2 - arr[i];
      var val2 := temp2 + count1 - temp1;
      if val1 == val2 {
        ans := ans + 1;
      }
      temp2 := temp2 + arr[i];
    }
  }

  result := ans;
}
