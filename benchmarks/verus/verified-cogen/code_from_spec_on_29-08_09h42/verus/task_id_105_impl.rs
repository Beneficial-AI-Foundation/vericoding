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
proof fn lemma_count_boolean_bounds(seq: Seq<bool>)
    ensures 0 <= count_boolean(seq) <= seq.len()
    decreases seq.len()
{
    if seq.len() == 0 {
    } else {
        lemma_count_boolean_bounds(seq.drop_last());
    }
}

proof fn lemma_count_boolean_prefix(seq: Seq<bool>, i: int)
    requires 0 <= i <= seq.len()
    ensures count_boolean(seq.subrange(0, i)) <= i
    decreases i
{
    if i == 0 {
    } else {
        lemma_count_boolean_prefix(seq, i - 1);
        assert(seq.subrange(0, i).drop_last() =~= seq.subrange(0, i - 1));
        assert(seq.subrange(0, i).last() == seq[i - 1]);
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
        lemma_count_boolean_bounds(arr@);
    }
    
    /* code modified by LLM (iteration 2): added decreases clause to fix verification error */
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
            assert(arr@.subrange(0, (i + 1) as int).drop_last() =~= arr@.subrange(0, i as int));
            assert(arr@.subrange(0, (i + 1) as int).last() == arr@[i as int]);
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