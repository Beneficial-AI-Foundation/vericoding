use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn multiset_remove_lemma<T>(s: Seq<T>, val: T, i: int)
    requires 0 <= i < s.len(), s[i] == val
    ensures s.to_multiset() == s.subrange(0, i).add(s.subrange(i + 1, s.len() as int)).to_multiset().insert(val)
{
    let left = s.subrange(0, i);
    let right = s.subrange(i + 1, s.len() as int);
    let combined = left.add(right);
    
    assert(s =~= left.add(seq![val]).add(right));
    assert(left.add(seq![val]).add(right).to_multiset() == 
           combined.to_multiset().insert(val));
}

proof fn swap_preserves_multiset<T>(v: Vec<T>, i: usize, j: usize)
    requires 0 <= i < v.len(), 0 <= j < v.len()
    ensures 
        ({
            let mut v_new = v;
            let temp = v_new[i as int];
            v_new.set(i, v_new[j as int]);
            v_new.set(j, temp);
            v_new@.to_multiset() == v@.to_multiset()
        })
{
    let mut v_new = v;
    let temp = v_new[i as int];
    v_new.set(i, v_new[j as int]);
    v_new.set(j, temp);
}
// </vc-helpers>

// <vc-spec>
fn remove_element(nums: &mut Vec<i32>, val: i32) -> (newLength: usize)
    ensures 
        0 <= newLength <= nums.len(),
        forall|i: int| 0 <= i < newLength ==> nums[i] != val,
        nums@.subrange(0, newLength as int).to_multiset() == 
            old(nums)@.to_multiset().remove(val),
// </vc-spec>
// <vc-code>
{
    let mut write_index: usize = 0;
    let mut read_index: usize = 0;
    let original_multiset = nums@.to_multiset();
    
    while read_index < nums.len()
        invariant
            0 <= write_index <= read_index <= nums.len(),
            forall|i: int| 0 <= i < write_index ==> nums[i] != val,
            nums@.subrange(0, write_index as int).to_multiset().add(
                nums@.subrange(read_index as int, nums.len() as int).filter(|x: i32| x == val).to_multiset()
            ) == original_multiset.remove(val),
    {
        if nums[read_index] != val {
            nums.set(write_index, nums[read_index]);
            write_index += 1;
        }
        read_index += 1;
    }
    
    write_index
}
// </vc-code>

fn main() {
}

}