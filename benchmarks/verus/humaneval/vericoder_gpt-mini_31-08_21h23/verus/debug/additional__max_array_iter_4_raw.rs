```vc-helpers
// Added helper lemmas to assist verification in the main implementation.
proof fn le_trans_lt(a: i32, b: i32, c: i32)
    requires
        a <= b,
        b < c,
    ensures
        a <= c,
{
    // From a <= b and b < c we get a < c, hence a <= c.
    assert(a <= c);
}

proof fn forall_le_update(nums: &[i32], old: usize, i: usize)
    requires
        old < nums.len(),
        i < nums.len(),
        forall|j: int| 0 <= j && j < i as int ==> nums[j as usize] <= nums[old],
        nums[old] < nums[i],
    ensures
        forall|j: int| 0 <= j && j < i as int ==> nums[j as usize] <= nums[i],
{
    // Prove the universal property for an arbitrary j.
    // For any j with 0 <= j < i, we have nums[j] <= nums[old] and nums[old] < nums[i].
    // By le_trans_lt, nums[j] <= nums[i].
    proof {
        fix j: int;
        assume Hj: 0 <= j && j < i as int;
        // instantiate the forall assumption to get nums[j] <= nums[old]
        assert(nums[j as usize] <= nums[old]);
        // use transitivity lemma to conclude nums[j] <= nums[i]
        le_trans_lt(nums[j as usize], nums[old], nums[i]);
    }
}
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
            assert(nums[i] > nums[old]);
            max_idx = i;
            // Use helper to show for all j < i: nums[j] <= nums[i] (now nums[max_idx])
            forall_le_update(nums, old, i);
            // nums[i] <= nums[max_idx] holds since max_idx == i
            assert(nums[i] <= nums[max_idx]);
            // Combine to establish for all j < i+1
            assert(forall|j: int| 0 <= j && j < (i as int) + 1 ==> nums[j as usize] <= nums[max_idx]);
        } else {
            // max_idx unchanged; for j < i it holds by invariant; for j == i it holds by branch condition
            assert(nums[i] <= nums[max_idx]);
            assert(forall|j: int| 0 <= j && j < (i as int) + 1 ==> nums[j as usize] <= nums[max_idx]);
        }
        i = i + 1;
    }
    // after loop, i == n and invariant gives property for all j < n
    max_idx
    // impl-end
}
```