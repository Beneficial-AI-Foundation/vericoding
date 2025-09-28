use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_subrange_contains_preserved(s1: Seq<i32>, s2: Seq<i32>, len: int, idx: int, val: i32)
    requires
        0 <= len <= s1.len(),
        0 <= idx < s1.len(),
        len <= idx,
        s1.subrange(0, len).contains(val),
    ensures
        s2.update(idx, val).subrange(0, len).contains(val),
{
}

proof fn lemma_distinct_preserved(s: Seq<i32>, idx: int, val: i32, write_idx: int)
    requires
        0 <= idx < s.len(),
        0 <= write_idx <= idx,
        forall|i: int, j: int| 0 <= i < j < write_idx ==> s[i] != s[j],
        forall|i: int| 0 <= i < write_idx ==> s[i] != val,
    ensures
        forall|i: int, j: int| 0 <= i < j < write_idx + 1 ==> s.update(idx, val)[i] != s.update(idx, val)[j],
{
}
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
    if nums.len() == 0 {
        return 0;
    }
    
    let mut write_idx: usize = 1;
    let mut read_idx: usize = 1;
    
    while read_idx < nums.len()
        invariant
            nums.len() == old(nums).len(),
            1 <= write_idx <= read_idx + 1,
            read_idx <= nums.len(),
            write_idx <= nums.len(),
            forall|i: int, j: int| 0 <= i < j < write_idx ==> nums[i] != nums[j],
            forall|i: int| 0 <= i < write_idx ==> old(nums)@.contains(nums[i]),
            forall|i: int| read_idx <= i < nums.len() ==> nums[i] == old(nums)[i],
            forall|i: int| 0 <= i < read_idx ==> (
                exists|j: int| 0 <= j < write_idx && nums[j] == old(nums)[i]
            ),
        decreases nums.len() - read_idx
    {
        if nums[read_idx] != nums[write_idx - 1] {
            let val = nums[read_idx];
            
            proof {
                assert(forall|i: int| 0 <= i < write_idx ==> nums[i] != val) by {
                    if exists|i: int| 0 <= i < write_idx && nums[i] == val {
                        let i = choose|i: int| 0 <= i < write_idx && nums[i] == val;
                        assert(old(nums)@.contains(nums[i]));
                        assert(old(nums)@.contains(val));
                        assert(nums[write_idx - 1] != val);
                    }
                };
            }
            
            nums.set(write_idx, val);
            write_idx += 1;
        }
        read_idx += 1;
    }
    
    proof {
        assert(write_idx <= nums.len());
        assert(forall|i: int| 0 <= i < old(nums).len() ==> (
            exists|j: int| 0 <= j < write_idx && nums[j] == old(nums)[i]
        ));
        assert(forall|i: int| 0 <= i < old(nums).len() ==> nums@.subrange(0, write_idx as int).contains(old(nums)[i])) by {
            assert(0 <= write_idx <= nums.len());
            assert(forall|i: int| 0 <= i < old(nums).len() ==> (
                exists|j: int| 0 <= j < write_idx && nums[j] == old(nums)[i]
            ));
        };
    }
    
    write_idx
}
// </vc-code>

fn main() {
}

}