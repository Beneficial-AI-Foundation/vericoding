```vc-helpers
// <vc-helpers>
// No helper functions needed for this proof.
// </vc-helpers>
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
        let old: usize = max_idx;
        if nums[i] > nums[old] {
            max_idx = i;
            assert(forall|j: int| 0 <= j && j < (i as int) + 1 ==> nums[j as usize] <= nums[max_idx]) by {
                fix j;
                assume Hj: 0 <= j && j < (i as int) + 1;
                if j < i as int {
                    // j < i: use invariant for old max_idx and nums[old] < nums[i]
                    assert(nums[j as usize] <= nums[old]);
                    assert(nums[old] < nums[i]);
                    assert(nums[j as usize] <= nums[max_idx]);
                } else {
                    // j == i
                    assert(j == i as int);
                    assert(nums[j as usize] <= nums[max_idx]);
                }
            };
        } else {
            // max_idx unchanged
            assert(forall|j: int| 0 <= j && j < (i as int) + 1 ==> nums[j as usize] <= nums[max_idx]) by {
                fix j;
                assume Hj: 0 <= j && j < (i as int) + 1;
                if j < i as int {
                    assert(nums[j as usize] <= nums[max_idx]);
                } else {
                    // j == i
                    assert(j == i as int);
                    assert(nums[i] <= nums[max_idx]);
                    assert(nums[j as usize] <= nums[max_idx]);
                }
            };
        }
        i = i + 1;
    }
    max_idx
    // impl-end
}
```