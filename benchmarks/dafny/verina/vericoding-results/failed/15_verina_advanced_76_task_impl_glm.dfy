// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): add reads clause */
function CountFrequency(nums: array<int>, value: int): nat
    reads nums
{
  |set i | 0 <= i < nums.Length :: nums[i] == value|
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
/* code modified by LLM (iteration 5): fix set initialization and adjust loops */
{
  if k == 0
  {
    result := new int[0];
  }
  else
  {
    var distinct := {}; // fixed: use empty set literal
    for i := 0 to nums.Length
    {
      distinct := distinct + {nums[i]};
    }
    var distinctCount := |distinct|;
    var distinctArr := new int[distinctCount];
    var freqArr := new int[distinctCount];
    var index := 0;
    for i := 0 to nums.Length
    {
      if nums[i] in distinct
      {
        distinctArr[index] := nums[i];
        freqArr[index] := CountFrequency(nums, nums[i]);
        distinct := distinct - {nums[i]};
        index := index + 1;
      }
    }
    for i := 0 to distinctCount
    {
      var maxIndex := i;
      var maxFreq := freqArr[i];
      for j := i+1 to distinctCount
      {
        if freqArr[j] > maxFreq
        {
          maxIndex := j;
          maxFreq := freqArr[j];
        }
      }
      var tempDistinct := distinctArr[i];
      distinctArr[i] := distinctArr[maxIndex];
      distinctArr[maxIndex] := tempDistinct;
      var tempFreq := freqArr[i];
      freqArr[i] := freqArr[maxIndex];
      freqArr[maxIndex] := tempFreq;
    }
    result := new int[k];
    for i := 0 to k
    {
      result[i] := distinctArr[i];
    }
  }
}
// </vc-code>
