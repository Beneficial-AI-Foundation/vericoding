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

predicate IsPermutation<T>(s1: seq<T>, s2: seq<T>) {
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

lemma DigitsSumPreserved(n: int)
  ensures digits_sum(n) >= 0
{}
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
}

method SortByDigitsSum(indexed_nums: seq<(int, int)>) returns (sorted: seq<(int, int)>)
  ensures |sorted| == |indexed_nums|
  ensures multiset(sorted) == multiset(indexed_nums)
  ensures forall i, j :: 0 <= i < j < |sorted| ==> 
    digits_sum(sorted[i].1) < digits_sum(sorted[j].1) ||
    (digits_sum(sorted[i].1) == digits_sum(sorted[j].1) && sorted[i].0 < sorted[j].0)
{
  sorted := indexed_nums;
  
  var i := 0;
  while i < |sorted|
    invariant 0 <= i <= |sorted|
    invariant |sorted| == |indexed_nums|
    invariant multiset(sorted) == multiset(indexed_nums)
  {
    var j := i;
    while j > 0 && (digits_sum(sorted[j-1].1) > digits_sum(sorted[j].1) ||
                    (digits_sum(sorted[j-1].1) == digits_sum(sorted[j].1) && sorted[j-1].0 > sorted[j].0))
      invariant 0 <= j <= i
      invariant |sorted| == |indexed_nums|
      invariant multiset(sorted) == multiset(indexed_nums)
    {
      sorted := sorted[j-1 := sorted[j]][j := sorted[j-1]];
      j := j - 1;
    }
    i := i + 1;
  }
}
// </vc-code>
