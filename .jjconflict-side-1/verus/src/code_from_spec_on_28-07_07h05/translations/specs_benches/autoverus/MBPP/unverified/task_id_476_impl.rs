#![verifier::loop_isolation(false)]
use vstd::math::*;
use vstd::prelude::*;

fn main() {}

verus! {

spec fn max_rcur(seq: Seq<i32>) -> int
    decreases seq.len(),
{
    if seq.len() <= 1 {
        seq.first() as int
    } else {
        max(seq.last() as int, max_rcur(seq.drop_last()))
    }
}

spec fn min_rcur(seq: Seq<i32>) -> int
    decreases seq.len(),
{
    if seq.len() <= 1 {
        seq.first() as int
    } else {
        min(seq.last() as int, min_rcur(seq.drop_last()))
    }
}

/* code modified by LLM (iteration 3): fixed lemma to properly prove the recursive relationship */
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
    let subseq = seq.subrange(0, i);
    if i == 1 {
        assert(subseq =~= seq![seq[0]]);
        assert(subseq.len() == 1);
        assert(max_rcur(subseq) == subseq.first() as int);
        assert(subseq.first() == seq[0]);
    } else {
        assert(subseq =~= seq.subrange(0, i-1).push(seq[i-1]));
        assert(subseq.len() > 1);
        assert(subseq.last() == seq[i-1]);
        assert(subseq.drop_last() == seq.subrange(0, i-1));
        assert(max_rcur(subseq) == max(subseq.last() as int, max_rcur(subseq.drop_last())));
        assert(max_rcur(subseq) == max(seq[i-1] as int, max_rcur(seq.subrange(0, i-1))));
    }
}

/* code modified by LLM (iteration 3): fixed lemma to properly prove the recursive relationship */
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
    let subseq = seq.subrange(0, i);
    if i == 1 {
        assert(subseq =~= seq![seq[0]]);
        assert(subseq.len() == 1);
        assert(min_rcur(subseq) == subseq.first() as int);
        assert(subseq.first() == seq[0]);
    } else {
        assert(subseq =~= seq.subrange(0, i-1).push(seq[i-1]));
        assert(subseq.len() > 1);
        assert(subseq.last() == seq[i-1]);
        assert(subseq.drop_last() == seq.subrange(0, i-1));
        assert(min_rcur(subseq) == min(subseq.last() as int, min_rcur(subseq.drop_last())));
        assert(min_rcur(subseq) == min(seq[i-1] as int, min_rcur(seq.subrange(0, i-1))));
    }
}

//IMPL sum_min_max
fn sum_min_max(arr: &Vec<i32>) -> (sum: i32)
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < #[trigger] arr[i] < i32::MAX / 2,
    ensures
        sum == max_rcur(arr@) + min_rcur(arr@),
{
    let mut max_val = arr[0];
    let mut min_val = arr[0];
    
    let mut i = 1;
    /* code modified by LLM (iteration 2): fixed loop invariants and added proof calls */
    while i < arr.len()
        invariant
            1 <= i <= arr.len(),
            max_val == max_rcur(arr@.subrange(0, i as int)),
            min_val == min_rcur(arr@.subrange(0, i as int)),
            i32::MIN / 2 < max_val < i32::MAX / 2,
            i32::MIN / 2 < min_val < i32::MAX / 2,
        decreases arr.len() - i,
    {
        /* code modified by LLM (iteration 2): moved lemma calls into proof block to fix compilation error */
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
    
    /* code modified by LLM (iteration 2): added assertion to establish postcondition */
    assert(i == arr.len());
    assert(arr@.subrange(0, arr.len() as int) == arr@);
    
    max_val + min_val
}

} // verus!