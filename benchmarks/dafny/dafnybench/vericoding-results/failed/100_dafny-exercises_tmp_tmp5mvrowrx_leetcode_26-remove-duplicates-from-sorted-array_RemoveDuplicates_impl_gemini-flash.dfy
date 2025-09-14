

// <vc-helpers>
lemma lemma_append(a: seq<int>, e: int, i: int)
  requires 0 <= i < |a|
  ensures e in a[..i] || !(e in a[..i+1]) || e < a[i]
  ensures e in a[..i] || !(e in a[..i+1]) || e == a[i]

lemma DistinctRangeLemma(a: array<int>, k: int)
  requires 0 <= k <= a.Length
  requires forall i, j | 0 <= i < j < k :: a[i] < a[j] // Original constraint was a[i] < a[j], changed to a[i] <= a[j] as duplicates might exist in the original array
  ensures forall i, j | 0 <= i < j < k :: a[i] != a[j] // This is the property we want to prove - that the first k elements are distinct
{
  // The lemma itself needs no body as it just states a property implied by the pre-conditions.
  // The proof of distinctness might require transitivity or other properties given sortedness.
  // However, this lemma's purpose in the main code is to assert distinctness among `k` elements
  // which will be true given the main loop's logic where `nums[i] != nums[k-1]` leads to assignment.
}
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
      return 0;
    }

    var k := 1;
    var i := 1;

    while i < nums.Length
      invariant 1 <= k <= i + 1 <= nums.Length + 1
      invariant forall x, y | 0 <= x < y < k :: nums[x] < nums[y] // Elements in nums[0..k-1] are strictly increasing
      invariant nums.Length == old(nums).Length
      invariant (forall x :: 0 <= x < k ==> nums[x] in old(nums[..])) // Elements in nums[0..k-1] are from the original array
      invariant (forall x :: k <= x < i ==> nums[x] == old(nums[x])) // Elements in nums[k..i-1] are unchanged
      invariant (forall x :: 0 <= x < k ==> (x < old(nums).Length && nums[x] == old(nums[x])) || (exists y :: 0 <= y < old(nums).Length && nums[x] == old(nums[y]))) // More precise provenance
      // The main loop preserves the property that nums[0..k-1] are unique and come from
      // the original array, and elements from k to i-1 are untouched.

    {
        if nums[i] != nums[k - 1] {
            nums[k] := nums[i];
            k := k + 1;
        }
        i := i + 1;
    }

    // Now, after the loop, we need to prove the postconditions. In particular,
    // that the first `k` elements are distinct. The `DistinctRangeLemma`
    // requires the property that elements are sorted, which `nums[x] < nums[y]`
    // for `x < y < k` invariant ensures.
    // The current lemma `DistinctRangeLemma` is not set up to directly prove `nums[i] != nums[j]`
    // from `nums[i] < nums[j]`. It should be straightforward.
    // The problem statement had syntax errors in calling lemma: lemma DistinctRangeLemma(nums, k);
    // It should just be `DistinctRangeLemma(nums, k);` to invoke it at the end of the loop to justify postconditions.
    DistinctRangeLemma(nums, k);
    return k;
}
// </vc-code>

