// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed invariant maintenance in frequency counting and sorting */
function Count(nums: seq<int>, x: int): nat
{
  if |nums| == 0 then 0
  else if nums[0] == x then 1 + Count(nums[1..], x)
  else Count(nums[1..], x)
}

lemma CountAppend(nums: seq<int>, x: int, y: int)
  ensures Count(nums + [y], x) == Count(nums, x) + (if x == y then 1 else 0)
{
  if |nums| == 0 {
    assert nums + [y] == [y];
  } else {
    assert (nums + [y])[1..] == nums[1..] + [y];
  }
}

method GetFrequencies(nums: array<int>) returns (freqMap: map<int, nat>)
  ensures forall x :: x in freqMap <==> x in nums[..]
  ensures forall x :: x in freqMap ==> freqMap[x] == Count(nums[..], x)
{
  freqMap := map[];
  var i := 0;
  while i < nums.Length
    invariant 0 <= i <= nums.Length
    invariant forall x :: x in freqMap <==> x in nums[..i]
    invariant forall x :: x in freqMap ==> freqMap[x] == Count(nums[..i], x)
  {
    var elem := nums[i];
    var oldCount := if elem in freqMap then freqMap[elem] else 0;
    assert nums[..i+1] == nums[..i] + [elem];
    CountAppend(nums[..i], elem, elem);
    assert Count(nums[..i+1], elem) == Count(nums[..i], elem) + 1;
    assert oldCount == Count(nums[..i], elem);
    
    var newMap := freqMap[elem := oldCount + 1];
    assert newMap[elem] == oldCount + 1 == Count(nums[..i+1], elem);
    assert forall x :: x != elem && x in newMap ==> newMap[x] == freqMap[x];
    assert forall x :: x != elem && x in newMap ==> newMap[x] == Count(nums[..i], x);
    CountAppend(nums[..i], x, elem);
    assert forall x :: x != elem && x in newMap ==> newMap[x] == Count(nums[..i+1], x);
    freqMap := newMap;
    
    i := i + 1;
  }
  assert nums[..] == nums[..nums.Length];
}

method SortByFrequency(elements: seq<int>, freqMap: map<int, nat>) returns (sorted: seq<int>)
  requires forall x :: x in elements ==> x in freqMap
  requires forall i, j :: 0 <= i < j < |elements| ==> elements[i] != elements[j]
  ensures |sorted| == |elements|
  ensures forall x :: x in sorted <==> x in elements
  ensures forall i, j :: 0 <= i < j < |sorted| ==> freqMap[sorted[i]] >= freqMap[sorted[j]]
{
  sorted := elements;
  var n := |sorted|;
  if n == 0 {
    return;
  }
  
  var i := 0;
  while i < n - 1
    invariant 0 <= i <= n - 1
    invariant |sorted| == |elements|
    invariant multiset(sorted) == multiset(elements)
    invariant forall x :: x in sorted <==> x in elements
    invariant forall p, q :: 0 <= p < q <= i ==> freqMap[sorted[p]] >= freqMap[sorted[q]]
    invariant forall p :: 0 <= p < i ==> forall q :: i <= q < n ==> freqMap[sorted[p]] >= freqMap[sorted[q]]
  {
    var j := i + 1;
    var maxIdx := i + 1;
    while j < n
      invariant i + 1 <= j <= n
      invariant i + 1 <= maxIdx < n
      invariant maxIdx <= j
      invariant forall p :: i + 1 <= p < j ==> freqMap[sorted[maxIdx]] >= freqMap[sorted[p]]
    {
      if freqMap[sorted[j]] > freqMap[sorted[maxIdx]] {
        maxIdx := j;
      }
      j := j + 1;
    }
    
    if freqMap[sorted[maxIdx]] > freqMap[sorted[i]] {
      var temp := sorted[i];
      var newSorted := sorted[i := sorted[maxIdx]][maxIdx := temp];
      assert multiset(newSorted) == multiset(sorted);
      sorted := newSorted;
    }
    i := i + 1;
  }
}
// </vc-helpers>

// <vc-spec>
method TopKFrequent(nums: array<int>, k: nat) returns (result: array<int>)
    requires k <= |set i | 0 <= i < nums.Length :: nums[i]|
    ensures result.Length == k
    ensures forall x :: x in result[..] ==> x in nums[..]
    ensures forall i, j :: 0 <= i < j < result.Length ==> result[i] != result[j]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed uniqueness assertions and invariant tracking */
{
  var freqMap := GetFrequencies(nums);
  
  var uniqueSet := freqMap.Keys;
  var uniqueElems: seq<int> := [];
  var seen: set<int> := {};
  
  while uniqueSet != {}
    invariant seen + uniqueSet == freqMap.Keys
    invariant forall x :: x in uniqueElems <==> x in seen
    invariant |uniqueElems| == |seen|
    invariant forall i, j :: 0 <= i < j < |uniqueElems| ==> uniqueElems[i] != uniqueElems[j]
    invariant forall x :: x in uniqueElems ==> x in freqMap
    decreases uniqueSet
  {
    var x :| x in uniqueSet;
    uniqueElems := uniqueElems + [x];
    seen := seen + {x};
    uniqueSet := uniqueSet - {x};
  }
  
  assert forall x :: x in uniqueElems ==> x in freqMap;
  assert forall i, j :: 0 <= i < j < |uniqueElems| ==> uniqueElems[i] != uniqueElems[j];
  assert |uniqueElems| == |seen|;
  assert seen == freqMap.Keys;
  assert |uniqueElems| == |freqMap.Keys|;
  
  assert forall x :: x in freqMap.Keys ==> x in nums[..];
  assert freqMap.Keys == set i | 0 <= i < nums.Length :: nums[i];
  assert |uniqueElems| >= k;
  
  var sortedElems := SortByFrequency(uniqueElems, freqMap);
  
  result := new int[k];
  var i := 0;
  while i < k
    invariant 0 <= i <= k
    invariant k <= |sortedElems|
    invariant forall j :: 0 <= j < i ==> result[j] in nums[..]
    invariant forall j :: 0 <= j < i ==> result[j] == sortedElems[j]
    invariant forall p, q :: 0 <= p < q < |sortedElems| ==> sortedElems[p] != sortedElems[q]
    invariant forall p, q :: 0 <= p < q < i ==> result[p] != result[q]
  {
    assert i < |sortedElems|;
    result[i] := sortedElems[i];
    assert forall p, q :: 0 <= p < q < |sortedElems| ==> sortedElems[p] != sortedElems[q];
    i := i + 1;
  }
}
// </vc-code>
