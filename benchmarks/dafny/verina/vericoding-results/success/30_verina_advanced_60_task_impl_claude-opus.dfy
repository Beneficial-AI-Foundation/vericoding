// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function CountEvens(nums: array<nat>, idx: nat): nat
  reads nums
  requires idx <= nums.Length
  decreases nums.Length - idx
{
  if idx == nums.Length then 0
  else if nums[idx] % 2 == 0 then 1 + CountEvens(nums, idx + 1)
  else CountEvens(nums, idx + 1)
}

function CountOdds(nums: array<nat>, idx: nat): nat
  reads nums
  requires idx <= nums.Length
  decreases nums.Length - idx
{
  if idx == nums.Length then 0
  else if nums[idx] % 2 == 1 then 1 + CountOdds(nums, idx + 1)
  else CountOdds(nums, idx + 1)
}
// </vc-helpers>

// <vc-spec>
method PartitionEvensOdds(nums: array<nat>) returns (evens: array<nat>, odds: array<nat>)
    requires true
    ensures forall i :: 0 <= i < evens.Length ==> evens[i] % 2 == 0
    ensures forall i :: 0 <= i < odds.Length ==> odds[i] % 2 == 1
// </vc-spec>
// <vc-code>
{
  var evenCount := CountEvens(nums, 0);
  var oddCount := CountOdds(nums, 0);
  
  evens := new nat[evenCount];
  odds := new nat[oddCount];
  
  var evenIdx := 0;
  var oddIdx := 0;
  var i := 0;
  
  while i < nums.Length
    invariant 0 <= i <= nums.Length
    invariant 0 <= evenIdx <= evens.Length
    invariant 0 <= oddIdx <= odds.Length
    invariant evenIdx <= evenCount
    invariant oddIdx <= oddCount
    invariant forall j :: 0 <= j < evenIdx ==> evens[j] % 2 == 0
    invariant forall j :: 0 <= j < oddIdx ==> odds[j] % 2 == 1
    invariant evenIdx == CountEvens(nums, 0) - CountEvens(nums, i)
    invariant oddIdx == CountOdds(nums, 0) - CountOdds(nums, i)
  {
    if nums[i] % 2 == 0 {
      evens[evenIdx] := nums[i];
      evenIdx := evenIdx + 1;
    } else {
      odds[oddIdx] := nums[i];
      oddIdx := oddIdx + 1;
    }
    i := i + 1;
  }
}
// </vc-code>
