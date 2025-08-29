function digits_sum_pos(n: int): int
  requires n >= 0
{
  if n < 10 then n else digits_sum_pos(n / 10) + n % 10
}
function digits_sum(n: int): int {
  if n < 0 then digits_sum_pos(-n) else digits_sum_pos(n)
}

// <vc-helpers>
function SumOfDigits(n: int): int {
  digits_sum(n)
}

lemma SumOfDigitsNonNegative(n: int)
  ensures SumOfDigits(n) >= 0
{
  if n < 0 {
    assert SumOfDigits(n) == digits_sum_pos(-n);
  } else {
    assert SumOfDigits(n) == digits_sum_pos(n);
  }
}

lemma MultisetPreservation(arr: seq<(int, int)>, sorted: seq<(int, int)>)
  requires |sorted| == |arr|
  requires forall x :: x in sorted ==> x in arr
  requires forall x :: x in arr ==> x in sorted
  ensures multiset(sorted) == multiset(arr)
{
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def order_by_points(nums: List[int]) -> List[int]
Write a function which sorts the given list of integers in ascending order according to the sum of their digits. Note: if there are several items with similar sum of their digits, order them based on their index in original list.
*/
// </vc-description>

// <vc-spec>
method OrderByPoints(nums: seq<int>) returns (result: seq<int>)
  requires nums != []
  ensures |result| == |nums|
  ensures forall i, j :: 0 <= i < j < |result| ==> 
    SumOfDigits(result[i]) < SumOfDigits(result[j]) || 
    (SumOfDigits(result[i]) == SumOfDigits(result[j]) && 
     (exists k, l :: 0 <= k < l < |nums| && nums[k] == result[i] && nums[l] == result[j]))
  ensures multiset(result) == multiset(nums)
// </vc-spec>
// <vc-code>
{
  var indexedNums: seq<(int, int)> := [];
  var i := 0;
  while i < |nums|
    invariant 0 <= i <= |nums|
    invariant |indexedNums| == i
    invariant forall k :: 0 <= k < i ==> indexedNums[k] == (nums[k], k)
  {
    indexedNums := indexedNums + [(nums[i], i)];
    i := i + 1;
  }

  var sortedIndexed := MergeSortIndexed(indexedNums);
  var resultSeq: seq<int> := [];
  i := 0;
  while i < |sortedIndexed|
    invariant 0 <= i <= |sortedIndexed|
    invariant |resultSeq| == i
    invariant forall k :: 0 <= k < i ==> resultSeq[k] == sortedIndexed[k].0
  {
    resultSeq := resultSeq + [sortedIndexed[i].0];
    i := i + 1;
  }
  result := resultSeq;
  assert multiset(result) == multiset(nums);
}

method MergeSortIndexed(arr: seq<(int, int)>) returns (sorted: seq<(int, int)>)
  ensures |sorted| == |arr|
  ensures forall i, j :: 0 <= i < j < |sorted| ==> 
    SumOfDigits(sorted[i].0) < SumOfDigits(sorted[j].0) || 
    (SumOfDigits(sorted[i].0) == SumOfDigits(sorted[j].0) && sorted[i].1 <= sorted[j].1)
  ensures multiset(sorted) == multiset(arr)
{
  if |arr| <= 1 {
    sorted := arr;
    return;
  }

  var mid := |arr| / 2;
  var left := MergeSortIndexed(arr[..mid]);
  var right := MergeSortIndexed(arr[mid..]);
  sorted := MergeIndexed(left, right);
  assert multiset(sorted) == multiset(left) + multiset(right);
  assert multiset(left) + multiset(right) == multiset(arr[..mid]) + multiset(arr[mid..]);
  assert multiset(arr[..mid]) + multiset(arr[mid..]) == multiset(arr);
  assert multiset(sorted) == multiset(arr);
}

method MergeIndexed(left: seq<(int, int)>, right: seq<(int, int)>) returns (merged: seq<(int, int)>)
  ensures |merged| == |left| + |right|
  ensures forall i, j :: 0 <= i < j < |merged| ==> 
    SumOfDigits(merged[i].0) < SumOfDigits(merged[j].0) || 
    (SumOfDigits(merged[i].0) == SumOfDigits(merged[j].0) && merged[i].1 <= merged[j].1)
  ensures multiset(merged) == multiset(left) + multiset(right)
{
  merged := [];
  var i := 0;
  var j := 0;

  while i < |left| && j < |right|
    invariant 0 <= i <= |left|
    invariant 0 <= j <= |right|
    invariant |merged| == i + j
    invariant forall k, l :: 0 <= k < l < |merged| ==> 
      SumOfDigits(merged[k].0) < SumOfDigits(merged[l].0) || 
      (SumOfDigits(merged[k].0) == SumOfDigits(merged[l].0) && merged[k].1 <= merged[l].1)
    invariant multiset(merged) == multiset(left[..i]) + multiset(right[..j])
  {
    var leftVal := left[i].0;
    var rightVal := right[j].0;
    var leftIndex := left[i].1;
    var rightIndex := right[j].1;
    if SumOfDigits(leftVal) < SumOfDigits(rightVal) || 
       (SumOfDigits(leftVal) == SumOfDigits(rightVal) && leftIndex <= rightIndex) {
      merged := merged + [left[i]];
      i := i + 1;
    } else {
      merged := merged + [right[j]];
      j := j + 1;
    }
  }

  while i < |left|
    invariant 0 <= i <= |left|
    invariant j == |right|
    invariant |merged| == i + j
    invariant forall k, l :: 0 <= k < l < |merged| ==> 
      SumOfDigits(merged[k].0) < SumOfDigits(merged[l].0) || 
      (SumOfDigits(merged[k].0) == SumOfDigits(merged[l].0) && merged[k].1 <= merged[l].1)
    invariant multiset(merged) == multiset(left[..i]) + multiset(right[..j])
  {
    merged := merged + [left[i]];
    i := i + 1;
  }

  while j < |right|
    invariant 0 <= j <= |right|
    invariant i == |left|
    invariant |merged| == i + j
    invariant forall k, l :: 0 <= k < l < |merged| ==> 
      SumOfDigits(merged[k].0) < SumOfDigits(merged[l].0) || 
      (SumOfDigits(merged[k].0) == SumOfDigits(merged[l].0) && merged[k].1 <= merged[l].1)
    invariant multiset(merged) == multiset(left[..i]) + multiset(right[..j])
  {
    merged := merged + [right[j]];
    j := j + 1;
  }
  assert multiset(merged) == multiset(left) + multiset(right);
}
// </vc-code>
