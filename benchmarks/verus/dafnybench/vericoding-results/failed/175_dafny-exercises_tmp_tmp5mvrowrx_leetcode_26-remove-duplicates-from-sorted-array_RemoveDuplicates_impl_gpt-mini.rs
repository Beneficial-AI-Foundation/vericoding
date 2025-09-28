use vstd::prelude::*;

verus! {

// <vc-helpers>
// (no helpers required)
// </vc-helpers>

// <vc-spec>
fn remove_duplicates(nums: &mut Vec<i32>) -> (num_length: usize)
    requires
        forall|i: int, j: int| 0 <= i < j < old(nums).len() ==> old(nums)[i] <= old(nums)[j],
    ensures
        nums.len() == old(nums).len(),
        0 <= num_length <= nums.len(),
        forall|i: int, j: int| 0 <= i < j < num_length ==> nums[i] != nums[j],
        forall|i: int| 0 <= i < num_length ==> old(nums)@.contains(nums[i]),
        forall|i: int| 0 <= i < old(nums).len() ==> nums@.subrange(0, num_length as int).contains(old(nums)[i]),
// </vc-spec>
// <vc-code>
{
    let old_seq: Seq<i32> = nums@;
    let n_usize: usize = nums.len();

    if n_usize == 0 {
        return 0;
    }

    let mut k: usize = 1;
    let mut i: usize = 1;
    while i < n_usize
        invariant
            1 <= k && k <= n_usize,
            1 <= i && i <= n_usize,
            k <= i,
            // prefix 0..k has no duplicates
            forall|a: int, b: int| 0 <= a < b < (k as int) ==> nums@[a] != nums@[b],
            // prefix elements come from old_seq
            forall|j: int| 0 <= j < (k as int) ==> old_seq.contains(nums@[j]),
            // elements from i..n_usize are still equal to old_seq
            forall|j: int| (i as int) <= j < (n_usize as int) ==> nums@[j] == old_seq[j],
        decreases (n_usize - i)
    {
        if nums[i] != nums[k - 1] {
            nums[k] = nums[i];
            k += 1;
        }
        i += 1;
    }

    k
}
// </vc-code>

fn main() {
}

}