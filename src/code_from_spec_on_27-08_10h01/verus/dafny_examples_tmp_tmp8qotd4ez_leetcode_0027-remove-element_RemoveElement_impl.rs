use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn multiset_remove_lemma<T>(s: Seq<T>, val: T, i: int)
    requires 
        0 <= i < s.len(),
        s[i] == val,
    ensures
        s.to_multiset().remove(val) == s.subrange(0, i).to_multiset().add(s.subrange(i + 1, s.len() as int).to_multiset()).remove(val),
{
    assert(s =~= s.subrange(0, i).add(seq![s[i]]).add(s.subrange(i + 1, s.len() as int)));
    assert(s.to_multiset() == s.subrange(0, i).to_multiset().add(seq![s[i]].to_multiset()).add(s.subrange(i + 1, s.len() as int).to_multiset()));
    assert(seq![s[i]].to_multiset() == seq![val].to_multiset());
}

proof fn multiset_preserve_lemma<T>(s: Seq<T>, val: T, i: int)
    requires 
        0 <= i < s.len(),
        s[i] != val,
    ensures
        s.to_multiset().remove(val) == s.subrange(0, i).to_multiset().add(s.subrange(i + 1, s.len() as int).to_multiset()).remove(val),
{
    assert(s =~= s.subrange(0, i).add(seq![s[i]]).add(s.subrange(i + 1, s.len() as int)));
    assert(s.to_multiset() == s.subrange(0, i).to_multiset().add(seq![s[i]].to_multiset()).add(s.subrange(i + 1, s.len() as int).to_multiset()));
    assert(seq![s[i]].to_multiset().remove(val) == seq![s[i]].to_multiset());
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn remove_element(nums: &mut Vec<i32>, val: i32) -> (newLength: usize)
    ensures 
        0 <= newLength <= nums.len(),
        forall|i: int| 0 <= i < newLength ==> nums[i] != val,
        nums@.subrange(0, newLength as int).to_multiset() == 
            old(nums)@.to_multiset().remove(val),
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let mut write_idx: usize = 0;
    let ghost old_nums = nums@;
    let n = nums.len();
    
    for read_idx in 0..n
        invariant
            0 <= write_idx <= read_idx <= n,
            n == nums.len(),
            forall|i: int| 0 <= i < write_idx ==> nums[i] != val,
            nums@.subrange(0, write_idx as int).to_multiset() == 
                old_nums.subrange(0, read_idx as int).to_multiset().remove(val),
    {
        if nums[read_idx] != val {
            proof {
                multiset_preserve_lemma(old_nums.subrange(0, (read_idx + 1) as int), val, read_idx as int);
            }
            let temp_val = nums[read_idx];
            nums.set(write_idx, temp_val);
            write_idx += 1;
        } else {
            proof {
                multiset_remove_lemma(old_nums.subrange(0, (read_idx + 1) as int), val, read_idx as int);
            }
        }
    }
    
    proof {
        assert(old_nums.subrange(0, n as int) == old_nums);
    }
    
    write_idx
}
// </vc-code>

fn main() {
}

}