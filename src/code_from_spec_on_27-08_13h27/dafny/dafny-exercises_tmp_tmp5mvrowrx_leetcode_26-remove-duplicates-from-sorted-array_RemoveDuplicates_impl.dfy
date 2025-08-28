// <vc-helpers>
lemma InSliceImpliesInArray(arr: array<int>, slice: seq<int>, i: int)
  requires slice == arr[..]
  requires 0 <= i < |slice|
  ensures slice[i] in arr[..]
{
}

lemma OldInSliceMaintains(arr: array<int>, oldSlice: seq<int>, newSlice: seq<int>, idx: int, bound: int)
  requires oldSlice == arr[..]
  requires newSlice == arr[..bound]
  requires 0 <= idx < bound <= arr.Length
  ensures oldSlice[idx] in newSlice
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method RemoveDuplicates(nums: array<int>) returns (num_length: int)
  modifies nums
  requires forall i, j | 0 <= i < j < nums.Length :: nums[i] <= nums[j]
  ensures nums.Length == old(nums).Length
  ensures 0 <= num_length <= nums.Length
  ensures forall i, j | 0 <= i < j < num_length :: nums[i] != nums[j]
  ensures forall i | 0 <= i < num_length :: nums[i] in old(nums[..])
  ensures forall i | 0 <= i < nums.Length :: old(nums[i]) in nums[..num_length]
// </vc-spec>
// </vc-spec>

// <vc-code>
method RemoveDuplicatesImpl(nums: array<int>) returns (num_length: int)
  modifies nums
  requires forall i, j | 0 <= i < j < nums.Length :: nums[i] <= nums[j]
  ensures nums.Length == old(nums.Length)
  ensures 0 <= num_length <= nums.Length
  ensures forall i, j | 0 <= i < j < num_length :: nums[i] != nums[j]
  ensures forall i | 0 <= i < num_length :: nums[i] in old(nums[..])
  ensures forall i | 0 <= i < nums.Length :: old(nums[i]) in nums[..num_length]
{
  if nums.Length == 0 {
    return 0;
  }
  
  var writeIndex := 1;
  var readIndex := 1;
  var oldNums := nums[..];
  
  while readIndex < nums.Length
    invariant 1 <= writeIndex <= readIndex <= nums.Length
    invariant forall i, j | 0 <= i < j < writeIndex :: nums[i] != nums[j]
    invariant forall i | 0 <= i < writeIndex :: nums[i] in oldNums
    invariant forall i | 0 <= i < readIndex :: oldNums[i] in nums[..writeIndex]
    decreases nums.Length - readIndex
  {
    if nums[readIndex] != nums[writeIndex - 1] {
      if writeIndex != readIndex {
        nums[writeIndex] := nums[readIndex];
        assert nums[writeIndex] in oldNums;
        assert forall i | 0 <= i < writeIndex :: nums[i] in oldNums;
        assert forall i, j | 0 <= i < j < writeIndex + 1 :: nums[i] != nums[j];
      }
      writeIndex := writeIndex + 1;
    } else {
      assert oldNums[readIndex] in nums[..writeIndex];
    }
    readIndex := readIndex + 1;
    assert forall i | 0 <= i < readIndex :: oldNums[i] in nums[..writeIndex];
  }
  
  num_length := writeIndex;
}
// </vc-code>
