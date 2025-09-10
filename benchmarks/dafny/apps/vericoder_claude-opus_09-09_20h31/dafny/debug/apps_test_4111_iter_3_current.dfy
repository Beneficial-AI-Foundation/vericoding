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
lemma sum_even_indices_correctness(arr: seq<int>, start: int)
  requires 0 <= start <= |arr|
  requires forall i :: 0 <= i < |arr| ==> arr[i] >= 1
  ensures sum_even_indices(arr, start) >= 0
  decreases |arr| - start
{
  if start == |arr| {
    assert sum_even_indices(arr, start) == 0;
  } else {
    sum_even_indices_correctness(arr, start + 1);
    if start % 2 == 0 {
      assert arr[start] >= 1;
      assert sum_even_indices(arr, start) == arr[start] + sum_even_indices(arr, start + 1);
    } else {
      assert sum_even_indices(arr, start) == sum_even_indices(arr, start + 1);
    }
  }
}

lemma sum_odd_indices_correctness(arr: seq<int>, start: int)
  requires 0 <= start <= |arr|
  requires forall i :: 0 <= i < |arr| ==> arr[i] >= 1
  ensures sum_odd_indices(arr, start) >= 0
  decreases |arr| - start
{
  if start == |arr| {
    assert sum_odd_indices(arr, start) == 0;
  } else {
    sum_odd_indices_correctness(arr, start + 1);
    if start % 2 == 1 {
      assert arr[start] >= 1;
      assert sum_odd_indices(arr, start) == arr[start] + sum_odd_indices(arr, start + 1);
    } else {
      assert sum_odd_indices(arr, start) == sum_odd_indices(arr, start + 1);
    }
  }
}

lemma sum_even_indices_split(arr: seq<int>, i: int)
  requires 0 <= i <= |arr|
  ensures sum_even_indices(arr, 0) == sum_even_indices(arr[..i], 0) + sum_even_indices(arr[i..], 0 - i % 2)
  decreases i
{
  if i == 0 {
    assert arr[..0] == [];
    assert arr[0..] == arr;
    assert sum_even_indices([], 0) == 0;
  } else {
    sum_even_indices_split(arr, i - 1);
    var prev_sum := sum_even_indices(arr[..i-1], 0);
    var curr_elem := arr[i-1];
    assert arr[..i] == arr[..i-1] + [curr_elem];
    
    if (i-1) % 2 == 0 {
      assert sum_even_indices(arr[..i], 0) == prev_sum + curr_elem;
    } else {
      assert sum_even_indices(arr[..i], 0) == prev_sum;
    }
  }
}

lemma sum_odd_indices_split(arr: seq<int>, i: int)
  requires 0 <= i <= |arr|
  ensures sum_odd_indices(arr, 0) == sum_odd_indices(arr[..i], 0) + sum_odd_indices(arr[i..], 0 - i % 2)
  decreases i
{
  if i == 0 {
    assert arr[..0] == [];
    assert arr[0..] == arr;
    assert sum_odd_indices([], 0) == 0;
  } else {
    sum_odd_indices_split(arr, i - 1);
    var prev_sum := sum_odd_indices(arr[..i-1], 0);
    var curr_elem := arr[i-1];
    assert arr[..i] == arr[..i-1] + [curr_elem];
    
    if (i-1) % 2 == 1 {
      assert sum_odd_indices(arr[..i], 0) == prev_sum + curr_elem;
    } else {
      assert sum_odd_indices(arr[..i], 0) == prev_sum;
    }
  }
}

lemma count_helper_bounds(arr: seq<int>, i: int, count1: int, count2: int, temp1: int, temp2: int)
  requires 0 <= i <= |arr|
  ensures 0 <= count_helper(arr, i, count1, count2, temp1, temp2) <= |arr| - i
  decreases |arr| - i
{
  if i == |arr| {
  } else {
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
    count_helper_bounds(arr, i + 1, count1, count2, new_temp1, new_temp2);
    assert contribution == 0 || contribution == 1;
  }
}

lemma sum_even_build(arr: seq<int>, j: int)
  requires 0 <= j <= |arr|
  ensures sum_even_indices(arr[..j], 0) == if j == 0 then 0 else sum_even_indices(arr[..j-1], 0) + (if (j-1) % 2 == 0 then arr[j-1] else 0)
{
  if j == 0 {
    assert arr[..0] == [];
  } else {
    assert arr[..j] == arr[..j-1] + [arr[j-1]];
  }
}

lemma sum_odd_build(arr: seq<int>, j: int)
  requires 0 <= j <= |arr|
  ensures sum_odd_indices(arr[..j], 0) == if j == 0 then 0 else sum_odd_indices(arr[..j-1], 0) + (if (j-1) % 2 == 1 then arr[j-1] else 0)
{
  if j == 0 {
    assert arr[..0] == [];
  } else {
    assert arr[..j] == arr[..j-1] + [arr[j-1]];
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
  if n == 0 {
    return 0;
  }
  
  sum_even_indices_correctness(arr, 0);
  sum_odd_indices_correctness(arr, 0);
  
  var count1 := 0;
  var j := 0;
  while j < n
    invariant 0 <= j <= n
    invariant count1 == sum_even_indices(arr[..j], 0)
  {
    sum_even_build(arr, j + 1);
    if j % 2 == 0 {
      count1 := count1 + arr[j];
    }
    j := j + 1;
  }
  assert arr[..n] == arr;
  assert count1 == sum_even_indices(arr, 0);
  
  var count2 := 0;
  j := 0;
  while j < n
    invariant 0 <= j <= n
    invariant count2 == sum_odd_indices(arr[..j], 0)
  {
    sum_odd_build(arr, j + 1);
    if j % 2 == 1 {
      count2 := count2 + arr[j];
    }
    j := j + 1;
  }
  assert arr[..n] == arr;
  assert count2 == sum_odd_indices(arr, 0);
  
  result := 0;
  var temp1 := 0;
  var temp2 := 0;
  var i := 0;
  
  while i < n
    invariant 0 <= i <= n
    invariant 0 <= result <= i
    invariant temp1 == sum_even_indices(arr[..i], 0)
    invariant temp2 == sum_odd_indices(arr[..i], 0)
    invariant result == count_helper(arr, 0, count1, count2, 0, 0) - count_helper(arr, i, count1, count2, temp1, temp2)
  {
    sum_even_build(arr, i + 1);
    sum_odd_build(arr, i + 1);
    
    if i % 2 == 0 {
      var val1 := temp1 + count2 - temp2;
      var val2 := temp2 + count1 - temp1 - arr[i];
      if val1 == val2 {
        result := result + 1;
      }
      temp1 := temp1 + arr[i];
    } else {
      var val1 := temp1 + count2 - temp2 - arr[i];
      var val2 := temp2 + count1 - temp1;
      if val1 == val2 {
        result := result + 1;
      }
      temp2 := temp2 + arr[i];
    }
    i := i + 1;
  }
  
  assert i == n;
  assert arr[..n] == arr;
  assert temp1 == sum_even_indices(arr, 0);
  assert temp2 == sum_odd_indices(arr, 0);
  assert result == count_helper(arr, 0, count1, count2, 0, 0);
  assert result == count_balanced_removals(arr);
  count_helper_bounds(arr, 0, count1, count2, 0, 0);
}
// </vc-code>

