// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Added lemma to prove relationship between count_boolean of sequence and its extension */
proof fn count_boolean_bounds(seq: Seq<bool>)
    ensures
        0 <= count_boolean(seq) <= seq.len(),
    decreases seq.len(),
{
    if seq.len() == 0 {
    } else {
        count_boolean_bounds(seq.drop_last());
    }
}

proof fn count_boolean_extend(seq: Seq<bool>, i: int)
    requires
        0 <= i < seq.len(),
    ensures
        count_boolean(seq.subrange(0, i + 1)) == count_boolean(seq.subrange(0, i)) + if seq[i] { 1int } else { 0int },
    decreases seq.len() - i,
{
    let prefix = seq.subrange(0, i);
    let extended = seq.subrange(0, i + 1);
    assert(extended.drop_last() =~= prefix);
    assert(extended.last() == seq[i]);
}
// </vc-helpers>

// <vc-spec>
fn count_true(arr: &Vec<bool>) -> (count: u64)

    ensures
        0 <= count <= arr.len(),
        count_boolean(arr@) == count,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Fixed proof by using helper lemma for count_boolean extension property */
    let mut count: u64 = 0;
    let mut i: usize = 0;
    
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            0 <= count <= i,
            count == count_boolean(arr@.subrange(0, i as int)),
        decreases arr.len() - i,
    {
        proof {
            count_boolean_extend(arr@, i as int);
        }
        
        if arr[i] {
            count = count + 1;
        }
        i = i + 1;
    }
    
    proof {
        assert(arr@.subrange(0, arr.len() as int) =~= arr@);
        count_boolean_bounds(arr@);
    }
    
    count
}
// </vc-code>

}
fn main() {}