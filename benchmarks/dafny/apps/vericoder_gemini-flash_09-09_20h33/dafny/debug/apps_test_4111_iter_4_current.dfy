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
function sum_even_indices_prefix(arr: seq<int>, end: int): int
  requires 0 <= end <= |arr|
  decreases end
{
  if end == 0 then 0
  else
    var contribution := if (end - 1) % 2 == 0 then arr[end - 1] else 0;
    contribution + sum_even_indices_prefix(arr, end - 1)
}

function sum_odd_indices_prefix(arr: seq<int>, end: int): int
  requires 0 <= end <= |arr|
  decreases end
{
  if end == 0 then 0
  else
    var contribution := if (end - 1) % 2 == 1 then arr[end - 1] else 0;
    contribution + sum_odd_indices_prefix(arr, end - 1)
}

function sum_even_indices_range(arr: seq<int>, start: int, end: int): int
  requires 0 <= start <= end <= |arr|
  decreases end - start
{
  if start == end then 0
  else
    var contribution := if start % 2 == 0 then arr[start] else 0;
    contribution + sum_even_indices_range(arr, start + 1, end)
}

function sum_odd_indices_range(arr: seq<int>, start: int, end: int): int
  requires 0 <= start <= end <= |arr|
  decreases end - start
{
  if start == end then 0
  else
    var contribution := if start % 2 == 1 then arr[start] else 0;
    contribution + sum_odd_indices_range(arr, start + 1, end)
}

lemma lemma_sum_even_prefix_relation(arr: seq<int>, k: int)
  requires 0 <= k <= |arr|
  ensures sum_even_indices_prefix(arr, k) == sum_even_indices_range(arr, 0, k)
{
  if k == 0 {}
  else {
    lemma_sum_even_prefix_relation(arr, k - 1);
    var p_even_k_minus_1 := sum_even_indices_prefix(arr, k - 1);
    var r_even_k_minus_1 := sum_even_indices_range(arr, 0, k - 1);
    calc {
      sum_even_indices_prefix(arr, k);
      (if (k - 1) % 2 == 0 then arr[k - 1] else 0) + sum_even_indices_prefix(arr, k - 1);
      (if (k - 1) % 2 == 0 then arr[k - 1] else 0) + r_even_k_minus_1;
      sum_even_indices_range(arr, 0, k);
    }
  }
}

lemma lemma_sum_odd_prefix_relation(arr: seq<int>, k: int)
  requires 0 <= k <= |arr|
  ensures sum_odd_indices_prefix(arr, k) == sum_odd_indices_range(arr, 0, k)
{
  if k == 0 {}
  else {
    lemma_sum_odd_prefix_relation(arr, k - 1);
    var p_odd_k_minus_1 := sum_odd_indices_prefix(arr, k - 1);
    var r_odd_k_minus_1 := sum_odd_indices_range(arr, 0, k - 1);
    calc {
      sum_odd_indices_prefix(arr, k);
      (if (k - 1) % 2 == 1 then arr[k - 1] else 0) + sum_odd_indices_prefix(arr, k - 1);
      (if (k - 1) % 2 == 1 then arr[k - 1] else 0) + r_odd_k_minus_1;
      sum_odd_indices_range(arr, 0, k);
    }
  }
}

lemma lemma_split_count_helper(arr: seq<int>, i: int, k: int, count1: int, count2: int, temp1: int, temp2: int)
  requires 0 <= i <= k <= |arr|
  ensures count_helper(arr, i, count1, count2, temp1, temp2) ==
          (if i == k then 0 else
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
            contribution + count_helper(arr, i + 1, count1, count2, new_temp1, new_temp2))
{
  if i == k {
  } else {
    lemma_split_count_helper(arr, i + 1, k, count1, count2, 
      (if i % 2 == 0 then temp1 + arr[i] else temp1), 
      (if i % 2 == 1 then temp2 + arr[i] else temp2));
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
  var len := |arr>; // Changed `n` because it's redefined later
  if len == 0 {
    return 0;
  }

  var total_even_sum := sum_even_indices(arr, 0);
  var total_odd_sum := sum_odd_indices(arr, 0);

  var result := 0;
  var current_even_prefix_sum := 0;
  var current_odd_prefix_sum := 0;

  var i := 0;
  while i < len
    invariant 0 <= i <= len
    invariant result == (count_balanced_removals(arr) - count_helper(arr, i, total_even_sum, total_odd_sum, current_even_prefix_sum, current_odd_prefix_sum))
    invariant current_even_prefix_sum == sum_even_indices_range(arr, 0, i)
    invariant current_odd_prefix_sum == sum_odd_indices_range(arr, 0, i)
  {
    lemma_sum_even_prefix_relation(arr, i);
    lemma_sum_odd_prefix_relation(arr, i);

    lemma_split_count_helper(arr, i, i + 1, total_even_sum, total_odd_sum, current_even_prefix_sum, current_odd_prefix_sum);

    if i % 2 == 0 { // Element arr[i] is at an even index
      var even_sum_after_removal := current_even_prefix_sum + (total_odd_sum - current_odd_prefix_sum);
      var odd_sum_after_removal := current_odd_prefix_sum + (total_even_sum - (current_even_prefix_sum + arr[i])); // Corrected logic
      if even_sum_after_removal == odd_sum_after_removal {
        result := result + 1;
      }
      current_even_prefix_sum := current_even_prefix_sum + arr[i];
    } else { // Element arr[i] is at an odd index
      var even_sum_after_removal := current_even_prefix_sum + (total_odd_sum - (current_odd_prefix_sum + arr[i])); // Corrected logic
      var odd_sum_after_removal := current_odd_prefix_sum + (total_even_sum - current_even_prefix_sum);
      if even_sum_after_removal == odd_sum_after_removal {
        result := result + 1;
      }
      current_odd_prefix_sum := current_odd_prefix_sum + arr[i];
    }
    i := i + 1;
  }
  return result;
}
// </vc-code>

