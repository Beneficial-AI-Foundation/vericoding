// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Added lemma to prove equivalence between set comprehensions */
function Count(nums: seq<int>, x: int): nat { if |nums| == 0 then 0 else (if nums[0] == x then 1 else 0) + Count(nums[1..], x) }

function UniqueElements(nums: seq<int>): set<int> { set i | 0 <= i < |nums| :: nums[i] }

lemma UniqueElementsEquivalence(nums: seq<int>)
  ensures UniqueElements(nums) == (set i | 0 <= i < |nums| :: nums[i])
{
}

method ComputeTopKFrequent(nums: seq<int>, k: nat) returns (topK: seq<int>)
  requires k <= |UniqueElements(nums)|
  ensures |topK| == k
  ensures forall x :: x in topK ==> x in nums
  ensures forall i, j :: 0 <= i < j < |topK| ==> topK[i] != topK[j]
{
  var elements := UniqueElements(nums);
  var remaining := elements;
  var selected: set<int> := {};
  topK := [];
  
  while |topK| < k
    invariant |topK| <= k
    invariant |selected| == |topK|
    invariant remaining + selected == elements
    invariant remaining * selected == {}
    invariant forall x :: x in topK ==> x in nums
    invariant forall x :: x in topK ==> x in selected
    invariant forall i, j :: 0 <= i < j < |topK| ==> topK[i] != topK[j]
    invariant forall i :: 0 <= i < |topK| ==> topK[i] in selected
    decreases k - |topK|
  {
    var maxElem := PickElement(remaining);
    var maxCount := Count(nums, maxElem);
    
    var elem := maxElem;
    var elems := remaining;
    while elems != {}
      invariant elem in elements
      invariant elem in remaining
      invariant Count(nums, elem) >= maxCount
      invariant elems <= remaining
      decreases |elems|
    {
      var e := PickElement(elems);
      if Count(nums, e) > Count(nums, elem) {
        elem := e;
      }
      elems := elems - {e};
    }
    
    topK := topK + [elem];
    selected := selected + {elem};
    remaining := remaining - {elem};
  }
}

method PickElement(s: set<int>) returns (elem: int)
  requires s != {}
  ensures elem in s
{
  elem :| elem in s;
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
/* code modified by LLM (iteration 4): Fixed assertion by using lemma to prove set equivalence */
{
  if k == 0 {
    result := new int[0];
    return;
  }
  
  var uniqueSet := set i | 0 <= i < nums.Length :: nums[i];
  UniqueElementsEquivalence(nums[..]);
  assert uniqueSet == UniqueElements(nums[..]);
  
  var topK := ComputeTopKFrequent(nums[..], k);
  result := new int[k];
  var i := 0;
  while i < k
    invariant 0 <= i <= k
    invariant i <= |topK|
    invariant forall j :: 0 <= j < i ==> result[j] == topK[j]
  {
    result[i] := topK[i];
    i := i + 1;
  }
}
// </vc-code>
