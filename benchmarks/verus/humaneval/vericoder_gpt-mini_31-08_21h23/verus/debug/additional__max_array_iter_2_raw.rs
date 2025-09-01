```vc-helpers
fn le_trans_le_lt(a: i32, b: i32, c: i32)
    requires
        a <= b,
        b < c,
    ensures
        a <= c,
{
    proof {
        // From a <= b and b < c we get a < c, hence a <= c.
        assert(a <= c);
    }
}
```

```vc-code
{
    // impl-start
    let n: int = nums.len() as int;
    let mut max_idx: int = 0;
    let mut i: int = 1;
    while i < n
        invariant
            1 <= n,
            0 <= max_idx,
            max_idx < n,
            0 <= i,
            i <= n,
            forall|j: int| 0 <= j && j < i ==> nums[j] <= nums[max_idx],
    {
        if nums[i] > nums[max_idx] {
            let old: int = max_idx;
            // remember the relation before updating
            assert(nums[i] > nums[old]);
            max_idx = i;
            // need to establish invariant for j < i with new max_idx (which equals i)
            assert(forall|j: int| 0 <= j && j < i ==>
                // proof for each j: nums[j] <= nums[old] and nums[old] < nums[i] imply nums[j] <= nums[i]
                nums[j] <= nums[max_idx]) by {
                    fix j;
                    assume Hj: 0 <= j && j < i;
                    // from loop invariant before update
                    assert(nums[j] <= nums[old]);
                    assert(nums[old] < nums[i]);
                    le_trans_le_lt(nums[j], nums[old], nums[i]);
                    assert(nums[j] <= nums[i]);
                };
            // also trivially nums[i] <= nums[max_idx] (equal indices)
            assert(nums[i] <= nums[max_idx]);
            // combine for j < i+1
            assert(forall|j: int| 0 <= j && j < i + 1 ==> nums[j] <= nums[max_idx]);
        } else {
            // max_idx unchanged; need to show property holds for j < i+1
            assert(nums[i] <= nums[max_idx]);
            assert(forall|j: int| 0 <= j && j < i + 1 ==> nums[j] <= nums[max_idx]);
        }
        i = i + 1;
    }
    // after loop, i == n and invariant gives property for all j < n
    max_idx as usize
    // impl-end
}
```