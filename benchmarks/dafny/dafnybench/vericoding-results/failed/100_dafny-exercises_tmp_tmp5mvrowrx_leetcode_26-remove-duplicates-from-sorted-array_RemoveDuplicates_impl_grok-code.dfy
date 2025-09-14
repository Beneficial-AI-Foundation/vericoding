

// <vc-helpers>
// Updated helper code and proofs to fix verification errors
// No additional helpers needed
// </vc-helpers>

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
// <vc-code>
{
    if nums.Length == 0 {
        num_length := 0;
    } else {
        var slow := 0;
        var fast := 1;
        while fast < nums.Length
        invariant 0 <= slow < fast <= nums.Length
        invariant forall i,j | 0 <= i < j <= slow :: nums[i] <= nums[j]
        invariant forall i,j | 0 <= i < j <= slow :: nums[i] != nums[j]
        invariant forall p | 0 <= p < fast :: old(nums[p]) in nums[..slow+1]
        {
            if nums[fast] != nums[slow] {
                slow := slow + 1;
                nums[slow] := nums[fast];
            }
            fast := fast + 1;
        }
        num_length := slow + 1;
    }
}
// </vc-code>

