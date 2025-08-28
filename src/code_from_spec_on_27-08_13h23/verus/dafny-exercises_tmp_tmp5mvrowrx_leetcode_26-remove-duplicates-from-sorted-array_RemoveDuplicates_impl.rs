use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_contains_subrange<T>(seq: Seq<T>, sub_seq: Seq<T>, start: int, end: int)
    requires
        0 <= start <= end <= seq.len(),
        sub_seq == seq.subrange(start, end),
    ensures
        forall|i: int| 0 <= i < sub_seq.len() ==> seq.contains(sub_seq[i]),
{
}
// </vc-helpers>

// <vc-spec>
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
// </vc-spec>

// <vc-code>
fn remove_duplicates(nums: &mut Vec<i32>) -> (num_length: usize)
    requires
        forall|i: int, j: int| 0 <= i < j < old(nums).len() ==> old(nums)[i] <= old(nums)[j],
    ensures
        nums.len() == old(nums).len(),
        0 <= num_length <= nums.len(),
        forall|i: int, j: int| 0 <= i < j < num_length ==> nums[i] != nums[j],
        forall|i: int| 0 <= i < num_length ==> old(nums)@.contains(nums[i]),
        forall|i: int| 0 <= i < old(nums).len() ==> nums@.subrange(0, num_length as int).contains(old(nums)[i]),
{
    if nums.len() <= 1 {
        return nums.len();
    }

    let mut write_index: usize = 1;
    let mut read_index: usize = 1;

    while read_index < nums.len()
        invariant
            0 < write_index <= read_index <= nums.len(),
            nums.len() == old(nums).len(),
            forall|i: int, j: int| 0 <= i < j < write_index ==> nums[i] != nums[j],
            forall|i: int| 0 <= i < write_index ==> old(nums)@.contains(nums[i]),
            forall|i: int| 0 <= i < read_index ==> nums@.subrange(0, write_index as int).contains(old(nums)[i]),
    {
        if nums[read_index] != nums[write_index - 1] {
            if write_index != read_index {
                nums[write_index] = nums[read_index];
            }
            write_index = write_index + 1;
        }
        read_index = read_index + 1;
    }

    proof {
        lemma_contains_subrange(nums@, nums@.subrange(0, write_index as int), 0, write_index as int);
    }

    write_index
}
// </vc-code>

fn main() {
}

}