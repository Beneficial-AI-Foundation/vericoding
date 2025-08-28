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

proof fn count_boolean_prefix_property(seq: Seq<bool>, i: int)
    requires 0 <= i <= seq.len()
    ensures count_boolean(seq.subrange(0, i)) <= count_boolean(seq)
    decreases seq.len() - i
{
    if i == seq.len() {
        assert(seq.subrange(0, i) =~= seq);
    } else {
        count_boolean_prefix_property(seq, i + 1);
        if seq[i] {
            assert(count_boolean(seq.subrange(0, i + 1)) == count_boolean(seq.subrange(0, i)) + 1);
        } else {
            assert(count_boolean(seq.subrange(0, i + 1)) == count_boolean(seq.subrange(0, i)));
        }
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
    
    proof {
        count_boolean_bounds(arr@);
    }
    
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            0 <= count <= i,
            count == count_boolean(arr@.subrange(0, i as int)),
    {
        if arr[i] {
            count = count + 1;
        }
        
        proof {
            assert(arr@.subrange(0, i as int + 1) =~= arr@.subrange(0, i as int).push(arr@[i as int]));
            if arr[i] {
                assert(count_boolean(arr@.subrange(0, i as int + 1)) == count_boolean(arr@.subrange(0, i as int)) + 1);
            } else {
                assert(count_boolean(arr@.subrange(0, i as int + 1)) == count_boolean(arr@.subrange(0, i as int)));
            }
        }
        
        i = i + 1;
    }
    
    proof {
        assert(arr@.subrange(0, i as int) =~= arr@);
    }
    
    count
}
// </vc-code>

} // verus!

fn main() {}