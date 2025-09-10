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
function count_helper(arr: seq<int>, i: int, count1: int, count2: int, temp1: int, temp2: int): int
  requires 0 <= i <= |arr|
  decreases |arr| - i
{
  if i == |arr| then 0
  else
    var contribution :=
      if i % 2 == 0 then
        let val1 := temp1 + count2 - temp2;
        let val2 := temp2 + count1 - temp1 - arr[i];
        if val1 == val2 then 1 else 0
      else
        let val1 := temp1 + count2 - temp2 - arr[i];
        let val2 := temp2 + count1 - temp1;
        if val1 == val2 then 1 else 0;
    var new_temp1 := if i % 2 == 0 then temp1 + arr[i] else temp1;
    var new_temp2 := if i % 2 == 1 then temp2 + arr[i] else temp2;
    contribution + count_helper(arr, i + 1, count1, count2, new_temp1, new_temp2)
}

lemma CountBound(arr: seq<int>)
  ensures 0 <= count_balanced_removals(arr) <= |arr|
{
  if |arr| == 0 {
    calc {
      count_balanced_removals(arr);
    == 0;
    <= 0;
    }
    calc {
      0;
    <= count_balanced_removals(arr);
    }
  } else {
    var count1 := sum_even_indices(arr, 0);
    var count2 := sum_odd_indices(arr, 0);
    CountHelperLEMMA(arr, 0, count1, count2, 0, 0);
    assert count_balanced_removals(arr) == count_helper(arr, 0, count1, count2, 0, 0);
    assert 0 <= count_balanced_removals(arr) <= |arr|;
  }
}

lemma CountHelperLEMMA(arr: seq<int>, i: int, count1: int, count2: int, temp1: int, temp2: int)
  requires 0 <= i <= |arr|
  ensures 0 <= count_helper(arr, i, count1, count2, temp1, temp2) <= |arr| - i
  decreases |arr| - i
{
  if i == |arr| {
    assert 0 <= 0;
  } else {
    var contribution :=
      if i % 2 == 0 then
        let val1 := temp1 + count2 - temp2;
        let val2 := temp2 + count1 - temp1 - arr[i];
        if val1 == val2 then 1 else 0
      else
        let val1 := temp1 + count2 - temp2 - arr[i];
        let val2 := temp2 + count1 - temp1;
        if val1 == val2 then 1 else 0;
    var new_temp1 := if i % 2 == 0 then temp1 + arr[i] else temp1;
    var new_temp2 := if i % 2 == 1 then temp2 + arr[i] else temp2;
    CountHelperLEMMA(arr, i + 1, count1, count2, new_temp1, new_temp2);
    assert 0 <= contribution <= 1;
    assert 0 <= count_helper(arr, i + 1, count1, count2, new_temp1, new_temp2) <= |arr| - i - 1;
    assert 0 <= contribution + count_helper(arr, i + 1, count1, count2, new_temp1, new_temp2) <= 1 + (|arr| - i - 1);
    assert contribution + count_helper(arr, i + 1, count1, count2, new_temp1, new_temp2) <= |arr| - i;
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
  CountBound(arr);
  result := count_balanced_removals(arr);
}
// </vc-code>

