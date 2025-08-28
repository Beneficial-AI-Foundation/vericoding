use vstd::prelude::*;

verus! {

spec fn count_boolean(seq: Seq<bool>) -> (result: int)
    decreases seq.len(),
{
    if seq.len() == 0 {
        0
    } else {
        count_boolean(seq.drop_last()) + if (seq.last()) {
            1 as int
        } else {
            0 as int
        }
    }
}
// pure-end

// <vc-helpers>
proof fn count_boolean_bounds(seq: Seq<bool>)
    ensures 0 <= count_boolean(seq) <= seq.len()
    decreases seq.len()
{
    if seq.len() == 0 {
    } else {
        count_boolean_bounds(seq.drop_last());
    }
}

proof fn count_boolean_prefix_invariant(seq: Seq<bool>, i: int)
    requires 0 <= i <= seq.len()
    ensures count_boolean(seq.subrange(0, i)) <= i
    decreases seq.len() - i
{
    if i == 0 {
        assert(seq.subrange(0, 0) =~= Seq::<bool>::empty());
    } else {
        count_boolean_prefix_invariant(seq, i - 1);
        assert(seq.subrange(0, i) =~= seq.subrange(0, i - 1).push(seq[i - 1]));
    }
}
// </vc-helpers>

// <vc-spec>
fn count_true(arr: &Vec<bool>) -> (count: u64)
    // pre-conditions-start
    ensures
        0 <= count <= arr.len(),
        count_boolean(arr@) == count,
    // pre-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut count: u64 = 0;
    let mut i: usize = 0;
    
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            0 <= count <= i,
            count_boolean(arr@.subrange(0, i as int)) == count,
        decreases arr.len() - i,
    {
        proof {
            count_boolean_prefix_invariant(arr@, i as int + 1);
        }
        
        if arr[i] {
            count = count + 1;
        }
        i = i + 1;
    }
    
    proof {
        assert(arr@.subrange(0, arr.len() as int) =~= arr@);
    }
    
    count
}
// </vc-code>

} // verus!

fn main() {}