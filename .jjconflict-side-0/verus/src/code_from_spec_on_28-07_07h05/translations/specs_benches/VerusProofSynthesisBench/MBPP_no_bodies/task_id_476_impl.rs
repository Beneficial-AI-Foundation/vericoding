#![verifier::loop_isolation(false)]
use vstd::math::*;
use vstd::prelude::*;

verus! {

spec fn max_rcur(seq: Seq<i32>) -> (result:int)
    decreases seq.len(),
{
    if seq.len() <= 1 {
        seq.first() as int
    } else {
        max(seq.last() as int, max_rcur(seq.drop_last()))
    }
}
// pure-end

spec fn min_rcur(seq: Seq<i32>) -> (result:int)
    decreases seq.len(),
{
    if seq.len() <= 1 {
        seq.first() as int
    } else {
        min(seq.last() as int, min_rcur(seq.drop_last()))
    }
}
// pure-end

/* code modified by LLM (iteration 1): added helper lemma to prove subrange equivalence */
proof fn lemma_subrange_full<T>(seq: Seq<T>)
    ensures seq.subrange(0, seq.len() as int) == seq
{
}

fn sum_min_max(arr: &Vec<i32>) -> (sum: i32)
    // pre-conditions-start
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < #[trigger] arr[i] < i32::MAX / 2,
    // pre-conditions-end
    // post-conditions-start
    ensures
        sum == max_rcur(arr@) + min_rcur(arr@),
    // post-conditions-end
{
    let mut max_val = arr[0];
    let mut min_val = arr[0];
    
    let mut i = 1;
    /* code modified by LLM (iteration 1): updated loop invariants and added overflow prevention */
    while i < arr.len()
        invariant
            0 < i <= arr.len(),
            max_val == max_rcur(arr@.subrange(0, i as int)),
            min_val == min_rcur(arr@.subrange(0, i as int)),
            i32::MIN / 2 < max_val < i32::MAX / 2,
            i32::MIN / 2 < min_val < i32::MAX / 2,
        decreases arr.len() - i,
    {
        if arr[i] > max_val {
            max_val = arr[i];
        }
        if arr[i] < min_val {
            min_val = arr[i];
        }
        i += 1;
    }
    
    /* code modified by LLM (iteration 2): added proof that subrange equals full sequence */
    proof {
        lemma_subrange_full(arr@);
        assert(arr@.subrange(0, arr.len() as int) == arr@);
    }
    
    /* code modified by LLM (iteration 2): fixed assertion syntax by separating conditions */
    assert(i32::MIN < max_val as int + min_val as int);
    assert(max_val as int + min_val as int < i32::MAX);
    
    max_val + min_val
}

} // verus!

fn main() {}