```vc-helpers
// No helper functions needed for this proof.
```

```vc-code
{
    // impl-start
    let n: usize = nums.len();
    let mut max_idx: usize = 0;
    let mut i: usize = 1usize;
    while i < n
        invariant
            1usize <= n,
            i <= n,
            max_idx < n,
            forall|j: int| 0 <= j && j < i as int ==> nums[j as usize] <= nums[max_idx],
    {
        if nums[i] > nums[max_idx] {
            let old: usize = max_idx;
            // remember the relation before updating
            assert(nums[i] > nums[old]);

            // Prove that for all j < i+1, nums[j] <= nums[i].
            // For j < i: from the loop invariant we have nums[j] <= nums[old], and nums[old] < nums[i],
            // so nums[j] <= nums[i]. For j == i it's trivial.
            assert(forall|j: int| 0 <= j && j < (i as int) + 1 ==> nums[j as usize] <= nums[i]) by {
                fix j;
                assume Hj: 0 <= j && j < (i as int) + 1;
                if j < i as int {
                    // instantiate the loop invariant for this j (before updating max_idx, so max_idx == old)
                    assert(nums[j as usize] <= nums[old]);
                    assert(nums[old] < nums[i]);
                    assert(nums[j as usize] <= nums[i]);
                } else {
                    // j == i
                    assert(j == i as int);
                    assert(nums[j as usize] <= nums[i]);
                }
            }

            // Now perform the update
            max_idx = i;

            // Since max_idx == i, the previously proven forall gives the required invariant for i+1
            assert(forall|j: int| 0 <= j && j < (i as int) + 1 ==> nums[j as usize] <= nums[max_idx]);
        } else {
            // max_idx unchanged; need to show property holds for j < i+1
            // For j < i it holds by invariant; for j == i it holds by branch condition nums[i] <= nums[max_idx]
            assert(nums[i] <= nums[max_idx]);
            assert(forall|j: int| 0 <= j && j < (i as int) + 1 ==> nums[j as usize] <= nums[max_idx]) by {
                fix j;
                assume Hj: 0 <= j && j < (i as int) + 1;
                if j < i as int {
                    // from invariant
                    assert(nums[j as usize] <= nums[max_idx]);
                } else {
                    // j == i
                    assert(j == i as int);
                    assert(nums[j as usize] <= nums[max_idx]);
                }
            }
        }
        i = i + 1;
    }
    // after loop, i == n and invariant gives property for all j < n
    max_idx
    // impl-end
}
```