#[allow(unused_imports)]
use vstd::prelude::*;
fn main() {}

verus! {
spec fn seq_to_set_rec<A>(seq: Seq<A>) -> Set<A>
    decreases seq.len()
{
    if seq.len() == 0 {
        Set::empty()
    } else {
        seq_to_set_rec(seq.drop_last()).insert(seq.last())
    }
}

/// helper function showing that the resulting set contains all elements of the sequence
proof fn seq_to_set_rec_contains<A>(seq: Seq<A>)
    ensures forall |a| #[trigger] seq.contains(a) <==> seq_to_set_rec(seq).contains(a)
    decreases seq.len()
{
    if seq.len() > 0 {
        assert(forall |a| #[trigger] seq.drop_last().contains(a) <==> seq_to_set_rec(seq.drop_last()).contains(a)) by {
            seq_to_set_rec_contains(seq.drop_last());
        }

        assert(seq.ext_equal(seq.drop_last().push(seq.last())));
        assert forall |a| #[trigger] seq.contains(a) <==> seq_to_set_rec(seq).contains(a) by {
            if !seq.drop_last().contains(a) {
                if a == seq.last() {
                    assert(seq.contains(a));
                    assert(seq_to_set_rec(seq).contains(a));
                } else {
                    assert(!seq_to_set_rec(seq).contains(a));
                }
            }
        }
    }
}

/// helper function showing that the recursive definition matches the set comprehension one
proof fn seq_to_set_equal_rec<A>(seq: Seq<A>)
    ensures seq.to_set() == seq_to_set_rec(seq)
{
    assert(forall |n| #[trigger] seq.contains(n) <==> seq_to_set_rec(seq).contains(n)) by {
        seq_to_set_rec_contains(seq);
    }
    assert(forall |n| #[trigger] seq.contains(n) <==> seq.to_set().contains(n));
    assert(seq.to_set().ext_equal(seq_to_set_rec(seq)));
}

proof fn lemma_seq_push_to_set_insert<T>(s: Seq<T>, val: T)
ensures
    s.push(val).to_set() === s.to_set().insert(val),
{
    seq_to_set_equal_rec(s.push(val));
    assert(s.ext_equal(s.push(val).drop_last()));
    seq_to_set_equal_rec(s);
    assert(s.push(val).to_set() === seq_to_set_rec(s.push(val)));
    assert(s.push(val).to_set() === seq_to_set_rec(s.push(val).drop_last()).insert(val));
}

fn remove_duplicates(nums: Vec<i32>) -> (res: Vec<i32>)
ensures
    res@.no_duplicates(),
    nums@.to_set().ext_equal(res@.to_set())
{
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < nums.len()
        invariant
            0 <= i <= nums.len(),
            result@.no_duplicates(),
            result@.to_set().subset_of(nums@.to_set()),
            forall |j: int| 0 <= j < i ==> 
                (nums@[j] in result@.to_set() <==> 
                 exists |k: int| 0 <= k <= j && nums@[k] == nums@[j])
    {
        let current = nums[i];
        let mut found = false;
        let mut j = 0;
        
        while j < result.len()
            invariant
                0 <= j <= result.len(),
                found == exists |k: int| 0 <= k < j && result@[k] == current
        {
            if result[j] == current {
                found = true;
                break;
            }
            j += 1;
        }
        
        if !found {
            proof {
                lemma_seq_push_to_set_insert(result@, current);
            }
            result.push(current);
        }
        
        i += 1;
    }
    
    result
}
}