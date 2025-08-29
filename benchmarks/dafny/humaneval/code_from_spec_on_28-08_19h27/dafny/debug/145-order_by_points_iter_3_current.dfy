function digits_sum_pos(n: int): int
  requires n >= 0
{
  if n < 10 then n else digits_sum_pos(n / 10) + n % 10
}
function digits_sum(n: int): int {
  if n < 0 then digits_sum_pos(-n) else digits_sum_pos(n)
}

// <vc-helpers>
predicate ValidIndices<T>(s: seq<T>, indices: seq<int>) {
  |indices| == |s| &&
  (forall i :: 0 <= i < |indices| ==> 0 <= indices[i] < |s|) &&
  (forall i, j :: 0 <= i < j < |indices| ==> indices[i] != indices[j])
}

predicate IsPermutation(s1: seq<int>, s2: seq<int>) {
  multiset(s1) == multiset(s2)
}

predicate SortedByDigitsSum(nums: seq<int>, result: seq<int>, original_indices: seq<int>) {
  |result| == |nums| &&
  |original_indices| == |nums| &&
  ValidIndices(nums, original_indices) &&
  (forall i :: 0 <= i < |result| ==> result[i] == nums[original_indices[i]]) &&
  (forall i, j :: 0 <= i < j < |result| ==> 
    digits_sum(result[i]) < digits_sum(result[j]) ||
    (digits_sum(result[i]) == digits_sum(result[j]) && original_indices[i] < original_indices[j]))
}

lemma DigitsSumNonNegative(n: int)
  ensures digits_sum(n) >= 0
{
  if n >= 0 {
    DigitsSumPosNonNegative(n);
  } else {
    DigitsSumPosNonNegative(-n);
  }
}

lemma DigitsSumPosNonNegative(n: int)
  requires n >= 0
  ensures digits_sum_pos(n) >= 0
{
  if n < 10 {
    assert digits_sum_pos(n) == n >= 0;
  } else {
    DigitsSumPosNonNegative(n / 10);
    assert n % 10 >= 0;
  }
}

lemma IndexedNumsToResult(nums: seq<int>, indexed_nums: seq<(int, int)>, sorted: seq<(int, int)>, result: seq<int>)
  requires |indexed_nums| == |nums|
  requires forall i :: 0 <= i < |indexed_nums| ==> indexed_nums[i] == (i, nums[i])
  requires |sorted| == |indexed_nums|
  requires multiset(sorted) == multiset(indexed_nums)
  requires |result| == |sorted|
  requires forall i :: 0 <= i < |result| ==> result[i] == sorted[i].1
  ensures IsPermutation(nums, result)
{
  assert multiset(result) == multiset(seq(|sorted|, i requires 0 <= i < |sorted| => sorted[i].1));
  
  var indexed_values := seq(|indexed_nums|, i requires 0 <= i < |indexed_nums| => indexed_nums[i].1);
  assert indexed_values == nums;
  
  var sorted_values := seq(|sorted|, i requires 0 <= i < |sorted| => sorted[i].1);
  assert sorted_values == result;
  
  assert multiset(indexed_values) == multiset(sorted_values);
  assert multiset(nums) == multiset(result);
}

lemma SortedPropertyHolds(nums: seq<int>, indexed_nums: seq<(int, int)>, sorted: seq<(int, int)>, result: seq<int>)
  requires |indexed_nums| == |nums|
  requires forall i :: 0 <= i < |indexed_nums| ==> indexed_nums[i] == (i, nums[i])
  requires |sorted| == |indexed_nums|
  requires multiset(sorted) == multiset(indexed_nums)
  requires |result| == |sorted|
  requires forall i :: 0 <= i < |result| ==> result[i] == sorted[i].1
  requires forall i, j :: 0 <= i < j < |sorted| ==> 
    digits_sum(sorted[i].1) < digits_sum(sorted[j].1) ||
    (digits_sum(sorted[i].1) == digits_sum(sorted[j].1) && sorted[i].0 < sorted[j].0)
  ensures exists original_indices: seq<int> :: SortedByDigitsSum(nums, result, original_indices)
{
  var original_indices := seq(|sorted|, i requires 0 <= i < |sorted| => sorted[i].0);
  
  assert |original_indices| == |nums|;
  assert |result| == |nums|;
  
  assert forall i :: 0 <= i < |original_indices| ==> 0 <= original_indices[i] < |nums| by {
    forall i | 0 <= i < |original_indices|
      ensures 0 <= original_indices[i] < |nums|
    {
      assert sorted[i] in multiset(indexed_nums);
      assert sorted[i].0 < |nums|;
    }
  }
  
  assert forall i, j :: 0 <= i < j < |original_indices| ==> original_indices[i] != original_indices[j] by {
    forall i, j | 0 <= i < j < |original_indices|
      ensures original_indices[i] != original_indices[j]
    {
      assert sorted[i] in multiset(indexed_nums);
      assert sorted[j] in multiset(indexed_nums);
      assert sorted[i] != sorted[j];
    }
  }
  
  assert ValidIndices(nums, original_indices);
  
  assert forall i :: 0 <= i < |result| ==> result[i] == nums[original_indices[i]] by {
    forall i | 0 <= i < |result|
      ensures result[i] == nums[original_indices[i]]
    {
      assert result[i] == sorted[i].1;
      assert original_indices[i] == sorted[i].0;
      assert sorted[i] in multiset(indexed_nums);
      assert sorted[i] == (sorted[i].0, nums[sorted[i].0]);
    }
  }
  
  assert SortedByDigitsSum(nums, result, original_indices);
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def order_by_points(nums: List[int]) -> List[int]
Write a function which sorts the given list of integers in ascending order according to the sum of their digits. Note: if there are several items with similar sum of their digits, order them based on their index in original list.
*/
// </vc-description>

// <vc-spec>
method order_by_points(nums: seq<int>) returns (result: seq<int>)
  ensures |result| == |nums|
  ensures IsPermutation(nums, result)
  ensures exists original_indices: seq<int> :: SortedByDigitsSum(nums, result, original_indices)
// </vc-spec>
// <vc-code>
{
  var indexed_nums := seq(|nums|, i requires 0 <= i < |nums| => (i, nums[i]));
  
  var sorted_indexed := SortByDigitsSum(indexed_nums);
  
  result := seq(|sorted_indexed|, i requires 0 <= i < |sorted_indexed| => sorted_indexed[i].1);
  
  IndexedNumsToResult(nums, indexed_nums, sorted_indexed, result);
  SortedPropertyHolds(nums, indexed_nums, sorted_indexed, result);
}

method SortByDigitsSum(indexed_nums: seq<(int, int)>) returns (sorted: seq<(int, int)>)
  ensures |sorted| == |indexed_nums|
  ensures multiset(sorted) == multiset(indexed_nums)
  ensures forall i, j :: 0 <= i < j < |sorted| ==> 
    digits_sum(sorted[i].1) < digits_sum(sorted[j].1) ||
    (digits_sum(sorted[i].1) == digits_sum(sorted[j].1) && sorted[i].0 < sorted[j].0)
{
  sorted := indexed_nums;
  
  var i := 1;
  while i < |sorted|
    invariant 1 <= i <= |sorted|
    invariant |sorted| == |indexed_nums|
    invariant multiset(sorted) == multiset(indexed_nums)
    invariant forall k1, k2 :: 0 <= k1 < k2 < i ==> 
      digits_sum(sorted[k1].1) < digits_sum(sorted[k2].1) ||
      (digits_sum(sorted[k1].1) == digits_sum(sorted[k2].1) && sorted[k1].0 < sorted[k2].0)
  {
    var j := i;
    while j > 0 && (digits_sum(sorted[j-1].1) > digits_sum(sorted[j].1) ||
                    (digits_sum(sorted[j-1].1) == digits_sum(sorted[j].1) && sorted[j-1].0 > sorted[j].0))
      invariant 0 <= j <= i
      invariant |sorted| == |indexed_nums|
      invariant multiset(sorted) == multiset(indexed_nums)
      invariant forall k1, k2 :: 0 <= k1 < k2 < j ==> 
        digits_sum(sorted[k1].1) < digits_sum(sorted[k2].1) ||
        (digits_sum(sorted[k1].1) == digits_sum(sorted[k2].1) && sorted[k1].0 < sorted[k2].0)
      invariant forall k1, k2 :: j < k1 < k2 <= i ==> 
        digits_sum(sorted[k1].1) < digits_sum(sorted[k2].1) ||
        (digits_sum(sorted[k1].1) == digits_sum(sorted[k2].1) && sorted[k1].0 < sorted[k2].0)
      invariant j < i ==> forall k :: j < k <= i ==> 
        digits_sum(sorted[j].1) < digits_sum(sorted[k].1) ||
        (digits_sum(sorted[j].1) == digits_sum(sorted[k].1) && sorted[j].0 < sorted[k].0)
    {
      sorted := sorted[j-1 := sorted[j]][j := sorted[j-1]];
      j := j - 1;
    }
    i := i + 1;
  }
}
// </vc-code>
