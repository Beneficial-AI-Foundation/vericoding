use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn unique_elements(s: Seq<i32>, end: int) -> bool {
    forall|i: int, j: int| 0 <= i < j < end ==> s[i] != s[j]
}

spec fn contains_all_original(original: Seq<i32>, result: Seq<i32>, end: int) -> bool {
    forall|i: int| 0 <= i < original.len() ==> result.subrange(0, end).contains(original[i])
}

spec fn result_from_original(original: Seq<i32>, result: Seq<i32>, end: int) -> bool {
    forall|i: int| 0 <= i < end ==> original.contains(result[i])
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
{
    if nums.len() == 0 {
        return 0;
    }
    
    let mut write_pos: usize = 1;
    let mut read_pos: usize = 1;
    
    while read_pos < nums.len()
        invariant
            nums.len() == old(nums).len(),
            1 <= write_pos <= read_pos + 1,
            read_pos <= nums.len(),
            forall|i: int, j: int| 0 <= i < j < write_pos ==> nums@[i] != nums@[j],
            forall|i: int| 0 <= i < write_pos ==> old(nums)@.contains(nums@[i]),
            forall|i: int| 0 <= i < read_pos ==> nums@.subrange(0, write_pos as int).contains(old(nums)@[i]),
            forall|i: int| read_pos <= i < nums.len() ==> nums@[i] == old(nums)@[i],
        decreases nums.len() - read_pos
    {
        let old_write_pos = write_pos;
        let old_read_pos = read_pos;
        
        if nums[read_pos] != nums[write_pos - 1] {
            let val = nums[read_pos];
            nums.set(write_pos, val);
            write_pos = write_pos + 1;
        }
        read_pos = read_pos + 1;
        
        proof {
            assert(forall|i: int| 0 <= i < old_read_pos ==> nums@.subrange(0, old_write_pos as int).contains(old(nums)@[i]));
            if old(nums)@[old_read_pos as int] == nums@[old_write_pos - 1] {
                assert(nums@.subrange(0, write_pos as int).contains(old(nums)@[old_read_pos as int]));
            } else {
                assert(nums@[write_pos - 1] == old(nums)@[old_read_pos as int]);
                assert(nums@.subrange(0, write_pos as int).contains(old(nums)@[old_read_pos as int]));
            }
        }
    }
    
    write_pos
}
// </vc-code>

fn main() {
}

}