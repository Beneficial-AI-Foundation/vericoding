// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed array slice conversion and set comprehension syntax */
function CountOccurrences(nums: array<int>, value: int): nat
  requires nums != null
  reads nums
{
  if nums.Length == 0 then 0
  else CountOccurrences(nums[1..], value) + (if nums[0] == value then 1 else 0)
}

function UniqueElements(nums: array<int>): set<int>
  requires nums != null
  reads nums
{
  set x | x in nums[..]
}

function FrequencyMap(nums: array<int>): map<int, int>
  requires nums != null
  reads nums
{
  if nums.Length == 0 then map[]
  else
    var rest := FrequencyMap(nums[1..]);
    var key := nums[0];
    var count := if key in rest then rest[key] else 0;
    rest[key := count + 1]
}

function TopKFrequentValues(nums: array<int>, k: nat): set<int>
  requires nums != null
  requires k <= |set x | x in nums[..]|
  reads nums
  ensures |TopKFrequentValues(nums, k)| == k
  ensures forall x :: x in TopKFrequentValues(nums, k) ==> x in nums[..]
{
  if k == 0 then {}
  else
    var freqs := FrequencyMap(nums);
    var keysList : seq<int> := seq(set x | x in freqs.Keys);
    var sorted := SortByFrequency(keysList, freqs);
    set i | 0 <= i < k && i < |sorted| :: sorted[i]
}

function SortByFrequency(elements: seq<int>, freq: map<int, int>): seq<int>
  decreases |elements|
{
  if |elements| <= 1 then elements
  else
    var pivot := elements[0];
    var left : seq<int> := seq(x | x in elements[1..] where freq[x] > freq[pivot]);
    var middle : seq<int> := seq(x | x in elements[1..] where freq[x] == freq[pivot]);
    var right : seq<int> := seq(x | x in elements[1..] where freq[x] < freq[pivot]);
    SortByFrequency(left, freq) + [pivot] + middle + SortByFrequency(right, freq)
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
{
  /* code modified by LLM (iteration 5): Fixed set to sequence conversion and element assignment */
  result := new int[k];
  var uniqueValues := TopKFrequentValues(nums, k);
  var idx := 0;
  var valuesSeq : seq<int> := seq(x | x in uniqueValues);
  
  while idx < k
      invariant 0 <= idx <= k
      invariant forall i :: 0 <= i < idx ==> result[i] in uniqueValues
      invariant forall i, j :: 0 <= i < j < idx ==> result[i] != result[j]
  {
      result[idx] := valuesSeq[idx];
      idx := idx + 1;
  }
}
// </vc-code>
