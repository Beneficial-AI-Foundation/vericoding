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
lemma sum_even_indices_split(arr: seq<int>, start: int, j: int)
  requires 0 <= start <= j <= |arr|
  ensures sum_even_indices(arr, start) == sum_even_indices(arr, start, j) + sum_even_indices(arr, j)
  decreases j - start
{
  if start < j {
    var contribution := if start % 2 == 0 then arr[start] else 0;
    sum_even_indices_split(arr, start + 1, j);
    assert sum_even_indices(arr, start) == contribution + sum_even_indices(arr, start + 1);
  }
}

ghost function sum_even_indices(arr: seq<int>, start: int, end: int): int
  requires 0 <= start <= end <= |arr|
  decreases end - start
{
  if start == end then 0
  else
    var contribution := if start % 2 == 0 then arr[start] else 0;
    contribution + sum_even_indices(arr, start + 1, end)
}

lemma sum_odd_indices_split(arr: seq<int>, start: int, j: int)
  requires 0 <= start <= j <= |arr|
  ensures sum_odd_indices(arr, start) == sum_odd_indices(arr, start, j) + sum_odd_indices(arr, j)
  decreases j - start
{
  if start < j {
    var contribution := if start % 2 == 1 then arr[start] else 0;
    sum_odd_indices_split(arr, start + 1, j);
    assert sum_odd_indices(arr, start) == contribution + sum_odd_indices(arr, start + 1);
  }
}

ghost function sum_odd_indices(arr: seq<int>, start: int, end: int): int
  requires 0 <= start <= end <= |arr|
  decreases end - start
{
  if start == end then 0
  else
    var contribution := if start % 2 == 1 then arr[start] else 0;
    contribution + sum_odd_indices(arr, start + 1, end)
}

lemma count_helper_correct(arr: seq<int>, i: int, count1: int, count2: int, temp1: int, temp2: int)
  requires 0 <= i <= |arr|
  requires count1 == sum_even_indices(arr, 0)
  requires count2 == sum_odd_indices(arr, 0)
  requires temp1 == sum_even_indices(arr, 0, i)
  requires temp2 == sum_odd_indices(arr, 0, i)
  ensures count_helper(arr, i, count1, count2, temp1, temp2) == (
    if i == |arr| then 0
    else
      var contribution := 
        if i % 2 == 0 then
          (if temp1 + count2 - temp2 == temp2 + count1 - temp1 - arr[i] then 1 else 0)
        else
          (if temp1 + count2 - temp2 - arr[i] == temp2 + count1 - temp1 then 1 else 0);
      contribution + count_helper(arr, i + 1, count1, count2, 
        temp1 + (if i % 2 == 0 then arr[i] else 0),
        temp2 + (if i % 2 == 1 then arr[i] else 0))
  )
  decreases |arr| - i
{
  if i < |arr| {
    sum_even_indices_split(arr, 0, i);
    sum_even_indices_split(arr, 0, i + 1);
    sum_odd_indices_split(arr, 0, i);
    sum_odd_indices_split(arr, 0, i + 1);
    
    var new_temp1 := temp1 + (if i % 2 == 0 then arr[i] else 0);
    var new_temp2 := temp2 + (if i % 2 == 1 then arr[i] else 0);
    
    count_helper_correct(arr, i + 1, count1, count2, new_temp1, new_temp2);
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, arr: seq<int>) returns (result: int)
  requires ValidInput(n, arr)
  ensures 0 <= result <= n
  ensures result == count_balanced_removals(arr)
// </vc-spec>
// <vc-code>
{
  result := 0;
  var even_sum := 0;
  var odd_sum := 0;
  
  // Calculate total even and odd sums
  var idx := 0;
  while idx < n
    invariant 0 <= idx <= n
    invariant even_sum == sum_even_indices(arr, 0, idx)
    invariant odd_sum == sum_odd_indices(arr, 0, idx)
  {
    if idx % 2 == 0 {
      even_sum := even_sum + arr[idx];
    } else {
      odd_sum := odd_sum + arr[idx];
    }
    idx := idx + 1;
  }
  
  var temp_even := 0;
  var temp_odd := 0;
  idx := 0;
  
  while idx < n
    invariant 0 <= idx <= n
    invariant temp_even == sum_even_indices(arr, 0, idx)
    invariant temp_odd == sum_odd_indices(arr, 0, idx)
  {
    if idx % 2 == 0 {
      // Removing element at even index
      var left_even := temp_even;
      var left_odd := temp_odd;
      var right_even := even_sum - temp_even - arr[idx];
      var right_odd := odd_sum - temp_odd;
      
      // Re-index right part (even becomes odd, odd becomes even)
      if left_even + right_odd == left_odd + right_even {
        result := result + 1;
      }
      temp_even := temp_even + arr[idx];
    } else {
      // Removing element at odd index
      var left_even := temp_even;
      var left_odd := temp_odd;
      var right_even := even_sum - temp_even;
      var right_odd := odd_sum - temp_odd - arr[idx];
      
      // Re-index right part (even becomes odd, odd becomes even)
      if left_even + right_odd == left_odd + right_even {
        result := result + 1;
      }
      temp_odd := temp_odd + arr[idx];
    }
    idx := idx + 1;
  }
}
// </vc-code>

