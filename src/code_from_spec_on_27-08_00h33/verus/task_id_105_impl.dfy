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
proof fn count_boolean_bound(seq: Seq<bool>)
    ensures 0 <= count_boolean(seq) <= seq.len()
    decreases seq.len()
{
    if seq.len() == 0 {
    } else {
        count_boolean_bound(seq.drop_last());
    }
}

proof fn count_boolean_prefix(seq: Seq<bool>, i: int)
    requires 0 <= i <= seq.len()
    ensures count_boolean(seq.subrange(0, i)) <= count_boolean(seq)
    decreases seq.len() - i
{
    if i == seq.len() {
        assert(seq.subrange(0, i) =~= seq);
    } else {
        count_boolean_subrange_inc(seq, i);
        assert(count_boolean(seq.subrange(0, i + 1)) >= count_boolean(seq.subrange(0, i)));
        count_boolean_prefix(seq, i + 1);
        assert(count_boolean(seq.subrange(0, i + 1)) <= count_boolean(seq));
        assert(count_boolean(seq.subrange(0, i)) <= count_boolean(seq));
    }
}

proof fn count_boolean_subrange_inc(seq: Seq<bool>, i: int)
    requires 0 <= i < seq.len()
    ensures count_boolean(seq.subrange(0, i + 1)) == 
            count_boolean(seq.subrange(0, i)) + if seq[i] { 1int } else { 0int }
    decreases seq.len() - i
{
    let sub_i = seq.subrange(0, i);
    let sub_i_plus_1 = seq.subrange(0, i + 1);
    
    assert(sub_i_plus_1.drop_last() =~= sub_i);
    assert(sub_i_plus_1.last() == seq[i]);
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
        count_boolean_bound(arr@);
    }
    
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            0 <= count <= i,
            count_boolean(arr@.subrange(0, i as int)) == count,
        decreases arr.len() - i
    {
        proof {
            count_boolean_subrange_inc(arr@, i as int);
            count_boolean_prefix(arr@, i as int);
        }
        
        if arr[i] {
            count = count + 1;
        }
        i = i + 1;
    }
    
    proof {
        assert(arr@.subrange(0, i as int) =~= arr@);
        count_boolean_prefix(arr@, 0);
    }
    
    count
}
// </vc-code>

} // verus!

fn main() {}