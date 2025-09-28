use vstd::prelude::*;

verus! {

// <vc-helpers>
use vstd::multiset::*;

proof fn lemma_seq_subrange_to_multiset_remove<T>(s: Seq<T>, start: int, end: int) 
    requires
        0 <= start <= end <= s.len(),
    ensures
        s.subrange(start, end).to_multiset() == s.to_multiset().difference(s.subrange(start, end).to_multiset()),
    decreases end - start,
{
    if start >= end {
        assert(s.subrange(start, end) === Seq::empty());
        assert(s.subrange(start, end).to_multiset() === Multiset::empty());
        assert(s.to_multiset().difference(Multiset::empty()) === s.to_multiset());
    } else {
        lemma_seq_subrange_to_multiset_remove(s, start, end - 1);
        let elem = s[end - 1];
        assert(s.subrange(start, end) === s.subrange(start, end - 1).push(elem));
        assert(s.subrange(start, end).to_multiset() == 
               s.subrange(start, end - 1).to_multiset().insert(elem));
        assert(s.to_multiset().difference(s.subrange(start, end).to_multiset()) == 
               s.to_multiset().difference(s.subrange(start, end - 1).to_multiset()).difference(Multiset::empty().insert(elem)));
    }
}

proof fn lemma_multiset_remove_val<T>(ms: Multiset<T>, val: T) 
    ensures
        ms.remove(val) == ms.difference(Multiset::empty().insert(val)),
{
}

proof fn lemma_vec_len_unchanged<T>(v: &mut Vec<T>, v_old: Ghost<Vec<T>>) 
    ensures
        v.len() == v_old@.len(),
{
}

proof fn lemma_vec_contents_unchanged<T>(v: &mut Vec<T>, v_old: Ghost<Vec<T>>) 
    ensures
        v@ == v_old@,
{
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
    let mut i: usize = 0;
    let mut j: usize = 0;
    let old_nums = Ghost::new(nums@);
    
    while j < nums.len()
        invariant
            0 <= i <= j <= nums.len(),
            forall|k: int| 0 <= k < i ==> nums[k] != val,
            nums@.subrange(0, i as int).to_multiset() == 
                old_nums@.subrange(0, j as int).to_multiset().remove(val),
            nums@.subrange(j as int, nums.len() as int) == old_nums@.subrange(j as int, nums.len() as int),
            nums@.subrange(0, nums.len() as int) == old_nums@.subrange(0, nums.len() as int),
        decreases nums.len() - j,
    {
        let current = nums[j];
        if current != val {
            if i != j {
                nums.set(i, current);
            }
            proof {
                lemma_seq_subrange_to_multiset_remove(old_nums@, 0, j as int);
                lemma_multiset_remove_val(old_nums@.subrange(0, j as int).to_multiset(), val);
            }
            i = i + 1;
        } else {
            proof {
                lemma_seq_subrange_to_multiset_remove(old_nums@, 0, j as int);
                lemma_multiset_remove_val(old_nums@.subrange(0, j as int).to_multiset(), val);
            }
        }
        j = j + 1;
    }
    
    proof {
        lemma_seq_subrange_to_multiset_remove(old_nums@, 0, nums.len() as int);
        lemma_multiset_remove_val(old_nums@.to_multiset(), val);
        assert(old_nums@.to_multiset().remove(val) == 
               old_nums@.to_multiset().difference(Multiset::empty().insert(val)));
        assert(old_nums@.to_multiset().remove(val) == 
               nums@.subrange(0, i as int).to_multiset());
    }
    
    i
}
// </vc-code>

fn main() {
}

}