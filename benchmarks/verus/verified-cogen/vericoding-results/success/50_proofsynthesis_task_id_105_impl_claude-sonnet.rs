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
/* helper modified by LLM (iteration 5): added decreases clause to fix recursive function error */
proof fn count_boolean_bound_lemma(seq: Seq<bool>)
    ensures 0 <= count_boolean(seq) <= seq.len(),
    decreases seq.len(),
{
    if seq.len() == 0 {
    } else {
        count_boolean_bound_lemma(seq.drop_last());
    }
}

proof fn count_boolean_take_extend_lemma(seq: Seq<bool>, i: int)
    requires 0 <= i < seq.len(),
    ensures count_boolean(seq.take(i + 1)) == count_boolean(seq.take(i)) + if seq[i] { 1int } else { 0int },
    decreases i,
{
    if i == 0 {
        assert(seq.take(1) == seq![seq[0]]);
        assert(count_boolean(seq.take(0)) == 0);
        assert(seq.take(1).len() == 1);
        assert(seq.take(1).last() == seq[0]);
        assert(count_boolean(seq.take(1)) == count_boolean(seq.take(1).drop_last()) + if seq.take(1).last() { 1int } else { 0int });
        assert(seq.take(1).drop_last() == seq.take(0));
    } else {
        count_boolean_take_extend_lemma(seq, i - 1);
        assert(seq.take(i + 1).drop_last() == seq.take(i));
        assert(seq.take(i + 1).last() == seq[i]);
        assert(count_boolean(seq.take(i + 1)) == count_boolean(seq.take(i + 1).drop_last()) + if seq.take(i + 1).last() { 1int } else { 0int });
    }
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
    /* code modified by LLM (iteration 5): no changes needed from previous iteration */
    let mut count: u64 = 0;
    let mut i = 0;
    
    proof {
        count_boolean_bound_lemma(arr@);
    }
    
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            0 <= count <= i,
            count_boolean(arr@.take(i as int)) == count,
        decreases arr.len() - i,
    {
        proof {
            count_boolean_take_extend_lemma(arr@, i as int);
        }
        
        if arr[i] {
            count = count + 1;
        }
        i = i + 1;
    }
    
    proof {
        assert(arr@.take(arr.len() as int) == arr@);
    }
    
    count
}
// </vc-code>

}
fn main() {}