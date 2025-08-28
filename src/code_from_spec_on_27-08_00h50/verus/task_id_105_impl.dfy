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
proof fn count_boolean_nonneg(seq: Seq<bool>)
    ensures count_boolean(seq) >= 0
    decreases seq.len()
{
    if seq.len() == 0 {
    } else {
        count_boolean_nonneg(seq.drop_last());
    }
}

proof fn count_boolean_upper_bound(seq: Seq<bool>)
    ensures count_boolean(seq) <= seq.len()
    decreases seq.len()
{
    if seq.len() == 0 {
    } else {
        count_boolean_upper_bound(seq.drop_last());
    }
}

proof fn count_boolean_prefix_property(seq: Seq<bool>, i: int)
    requires 0 <= i < seq.len()
    ensures count_boolean(seq.subrange(0, i + 1)) == count_boolean(seq.subrange(0, i)) + if seq[i] { 1int } else { 0int }
{
    let prefix = seq.subrange(0, i + 1);
    let prev_prefix = seq.subrange(0, i);
    
    assert(prefix.len() == i + 1);
    assert(prev_prefix.len() == i);
    assert(prefix.drop_last() =~= prev_prefix);
    assert(prefix.last() == seq[i]);
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
        count_boolean_nonneg(arr@);
        count_boolean_upper_bound(arr@);
    }
    
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            0 <= count <= i,
            count_boolean(arr@.subrange(0, i as int)) == count,
        decreases arr.len() - i
    {
        if arr[i] {
            count = count + 1;
        }
        
        proof {
            count_boolean_prefix_property(arr@, i as int);
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