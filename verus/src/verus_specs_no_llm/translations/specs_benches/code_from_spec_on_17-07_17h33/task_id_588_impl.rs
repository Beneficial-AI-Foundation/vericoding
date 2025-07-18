#![verifier::loop_isolation(false)]
use vstd::math::*;
use vstd::prelude::*;

verus! {

spec fn max_rcur(seq: Seq<i32>) -> (result: int)
    decreases seq.len(),
{
    if seq.len() <= 1 {
        seq.first() as int
    } else {
        max(seq.last() as int, max_rcur(seq.drop_last()))
    }
}
// pure-end

spec fn min_rcur(seq: Seq<i32>) -> (result: int)
    decreases seq.len(),
{
    if seq.len() <= 1 {
        seq.first() as int
    } else {
        min(seq.last() as int, min_rcur(seq.drop_last()))
    }
}
// pure-end

/* code modified by LLM (iteration 1): Added lemma to establish relationship between prefix and full array */
proof fn lemma_max_rcur_extend(seq: Seq<i32>, i: int)
    requires
        0 < i <= seq.len(),
    ensures
        max_rcur(seq.subrange(0, i)) == if i == 1 {
            seq[0] as int
        } else {
            max(seq[i-1] as int, max_rcur(seq.subrange(0, i-1)))
        },
    decreases i,
{
    if i == 1 {
        assert(seq.subrange(0, 1) =~= seq![seq[0]]);
    } else {
        assert(seq.subrange(0, i).drop_last() =~= seq.subrange(0, i-1));
        assert(seq.subrange(0, i).last() == seq[i-1]);
    }
}

/* code modified by LLM (iteration 1): Added lemma for min_rcur */
proof fn lemma_min_rcur_extend(seq: Seq<i32>, i: int)
    requires
        0 < i <= seq.len(),
    ensures
        min_rcur(seq.subrange(0, i)) == if i == 1 {
            seq[0] as int
        } else {
            min(seq[i-1] as int, min_rcur(seq.subrange(0, i-1)))
        },
    decreases i,
{
    if i == 1 {
        assert(seq.subrange(0, 1) =~= seq![seq[0]]);
    } else {
        assert(seq.subrange(0, i).drop_last() =~= seq.subrange(0, i-1));
        assert(seq.subrange(0, i).last() == seq[i-1]);
    }
}

/* code modified by LLM (iteration 1): Fixed function implementation with proper invariants and overflow checking */
fn difference_max_min(arr: &Vec<i32>) -> (diff: i32)
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < #[trigger] arr[i] < i32::MAX / 2,
    ensures
        diff == max_rcur(arr@) - min_rcur(arr@),
{
    let mut max_val = arr[0];
    let mut min_val = arr[0];
    
    let mut i = 1;
    while i < arr.len()
        invariant
            1 <= i <= arr.len(),
            max_val as int == max_rcur(arr@.subrange(0, i as int)),
            min_val as int == min_rcur(arr@.subrange(0, i as int)),
            i32::MIN / 2 < max_val < i32::MAX / 2,
            i32::MIN / 2 < min_val < i32::MAX / 2,
        decreases arr.len() - i,
    {
        proof {
            lemma_max_rcur_extend(arr@, (i + 1) as int);
            lemma_min_rcur_extend(arr@, (i + 1) as int);
        }
        
        if arr[i] > max_val {
            max_val = arr[i];
        }
        if arr[i] < min_val {
            min_val = arr[i];
        }
        i += 1;
    }
    
    /* code modified by LLM (iteration 1): Added assertion to help prove postcondition */
    assert(arr@.subrange(0, arr.len() as int) =~= arr@);
    
    max_val - min_val
}

} // verus!

fn main() {}