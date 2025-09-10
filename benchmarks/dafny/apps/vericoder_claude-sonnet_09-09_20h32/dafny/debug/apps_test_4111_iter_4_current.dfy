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
function sum_of_even_indices(arr: seq<int>): int
{
  var indices := set i | 0 <= i < |arr| && i % 2 == 0;
  if indices == {} then 0 else
  sum_indices_values(arr, indices)
}

function sum_of_odd_indices(arr: seq<int>): int
{
  var indices := set i | 0 <= i < |arr| && i % 2 == 1;
  if indices == {} then 0 else
  sum_indices_values(arr, indices)
}

function sum_indices_values(arr: seq<int>, indices: set<int>): int
  requires forall i :: i in indices ==> 0 <= i < |arr|
  decreases indices
{
  if indices == {} then 0
  else
    var i := choose_element(indices);
    arr[i] + sum_indices_values(arr, indices - {i})
}

function choose_element(s: set<int>): int
  requires s != {}
  ensures choose_element(s) in s
{
  var i :| i in s; i
}

lemma sum_even_indices_equivalence(arr: seq<int>)
  ensures sum_even_indices(arr, 0) == sum_of_even_indices(arr)
{
  sum_even_indices_helper(arr, 0, set i | 0 <= i < |arr| && i % 2 == 0);
}

lemma sum_odd_indices_equivalence(arr: seq<int>)
  ensures sum_odd_indices(arr, 0) == sum_of_odd_indices(arr)
{
  sum_odd_indices_helper(arr, 0, set i | 0 <= i < |arr| && i % 2 == 1);
}

lemma sum_even_indices_helper(arr: seq<int>, start: int, indices: set<int>)
  requires 0 <= start <= |arr|
  requires indices == set i | start <= i < |arr| && i % 2 == 0
  ensures sum_even_indices(arr, start) == (if indices == {} then 0 else sum_indices_values(arr, indices))
  decreases |arr| - start
{
  if start == |arr| {
    assert indices == {};
  } else {
    var rest_indices := set i | start + 1 <= i < |arr| && i % 2 == 0;
    sum_even_indices_helper(arr, start + 1, rest_indices);
    
    if start % 2 == 0 {
      assert indices == {start} + rest_indices;
      if rest_indices != {} {
        sum_indices_distributive(arr, {start}, rest_indices);
      }
    } else {
      assert indices == rest_indices;
    }
  }
}

lemma sum_odd_indices_helper(arr: seq<int>, start: int, indices: set<int>)
  requires 0 <= start <= |arr|
  requires indices == set i | start <= i < |arr| && i % 2 == 1
  ensures sum_odd_indices(arr, start) == (if indices == {} then 0 else sum_indices_values(arr, indices))
  decreases |arr| - start
{
  if start == |arr| {
    assert indices == {};
  } else {
    var rest_indices := set i | start + 1 <= i < |arr| && i % 2 == 1;
    sum_odd_indices_helper(arr, start + 1, rest_indices);
    
    if start % 2 == 1 {
      assert indices == {start} + rest_indices;
      if rest_indices != {} {
        sum_indices_distributive(arr, {start}, rest_indices);
      }
    } else {
      assert indices == rest_indices;
    }
  }
}

lemma sum_indices_distributive(arr: seq<int>, s1: set<int>, s2: set<int>)
  requires forall i :: i in s1 ==> 0 <= i < |arr|
  requires forall i :: i in s2 ==> 0 <= i < |arr|
  requires s1 * s2 == {}
  ensures sum_indices_values(arr, s1 + s2) == sum_indices_values(arr, s1) + sum_indices_values(arr, s2)
  decreases s1, s2
{
  if s1 == {} {
    assert s1 + s2 == s2;
  } else if s2 == {} {
    assert s1 + s2 == s1;
  } else {
    var i := choose_element(s1);
    assert i in s1;
    assert i !in s2;
    assert s1 + s2 == {i} + ((s1 - {i}) + s2);
    sum_indices_distributive(arr, s1 - {i}, s2);
    assert sum_indices_values(arr, (s1 - {i}) + s2) == sum_indices_values(arr, s1 - {i}) + sum_indices_values(arr, s2);
    assert sum_indices_values(arr, s1) == arr[i] + sum_indices_values(arr, s1 - {i});
    assert sum_indices_values(arr, s1 + s2) == arr[i] + sum_indices_values(arr, (s1 - {i}) + s2);
  }
}

lemma count_helper_bounds(arr: seq<int>, i: int, count1: int, count2: int, temp1: int, temp2: int)
  requires 0 <= i <= |arr|
  requires temp1 >= 0 && temp2 >= 0
  requires forall j :: 0 <= j < |arr| ==> arr[j] >= 1
  ensures 0 <= count_helper(arr, i, count1, count2, temp1, temp2) <= |arr| - i
  decreases |arr| - i
{
  if i == |arr| {
    // Base case: count_helper returns 0
  } else {
    // Inductive case
    var contribution := 
      if i % 2 == 0 then
        var val1 := temp1 + count2 - temp2;
        var val2 := temp2 + count1 - temp1 - arr[i];
        if val1 == val2 then 1 else 0
      else
        var val1 := temp1 + count2 - temp2 - arr[i];
        var val2 := temp2 + count1 - temp1;
        if val1 == val2 then 1 else 0;
    
    assert 0 <= contribution <= 1;
    
    var new_temp1 := if i % 2 == 0 then temp1 + arr[i] else temp1;
    var new_temp2 := if i % 2 == 1 then temp2 + arr[i] else temp2;
    
    assert arr[i] >= 1;
    assert new_temp1 >= temp1 >= 0;
    assert new_temp2 >= temp2 >= 0;
    count_helper_bounds(arr, i + 1, count1, count2, new_temp1, new_temp2);
    
    assert count_helper(arr, i, count1, count2, temp1, temp2) == 
           contribution + count_helper(arr, i + 1, count1, count2, new_temp1, new_temp2);
  }
}

lemma count_balanced_removals_bounds(arr: seq<int>)
  requires forall j :: 0 <= j < |arr| ==> arr[j] >= 1
  ensures 0 <= count_balanced_removals(arr) <= |arr|
{
  var n := |arr|;
  if n == 0 {
    // Base case
  } else {
    count_helper_bounds(arr, 0, sum_even_indices(arr, 0), sum_odd_indices(arr, 0), 0, 0);
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
  
  var count1 := sum_even_indices(arr, 0);
  var count2 := sum_odd_indices(arr, 0);
  
  sum_even_indices_equivalence(arr);
  sum_odd_indices_equivalence(arr);
  count_balanced_removals_bounds(arr);
  
  result := count_helper(arr, 0, count1, count2, 0, 0);
  
  assert result == count_balanced_removals(arr);
  assert 0 <= result <= |arr|;
  assert |arr| == n;
}
// </vc-code>

