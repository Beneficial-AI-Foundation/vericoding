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

/* code modified by LLM (iteration 1): added helper lemma to prove equivalence between subrange and full sequence */
proof fn lemma_max_rcur_subrange_full(seq: Seq<i32>)
    requires seq.len() > 0
    ensures max_rcur(seq.subrange(0, seq.len() as int)) == max_rcur(seq)
{
    assert(seq.subrange(0, seq.len() as int) =~= seq);
}

/* code modified by LLM (iteration 1): added helper lemma to prove equivalence between subrange and full sequence */
proof fn lemma_min_rcur_subrange_full(seq: Seq<i32>)
    requires seq.len() > 0
    ensures min_rcur(seq.subrange(0, seq.len() as int)) == min_rcur(seq)
{
    assert(seq.subrange(0, seq.len() as int) =~= seq);
}

/* code modified by LLM (iteration 3): added lemma to prove step-wise max property */
proof fn lemma_max_rcur_step(seq: Seq<i32>, i: int)
    requires 
        seq.len() > 0,
        1 <= i < seq.len(),
    ensures 
        max_rcur(seq.subrange(0, i + 1)) == max(seq[i] as int, max_rcur(seq.subrange(0, i))),
    decreases seq.len() - i
{
    let sub_i = seq.subrange(0, i);
    let sub_i_plus_1 = seq.subrange(0, i + 1);
    
    assert(sub_i_plus_1.len() == i + 1);
    assert(sub_i_plus_1.last() == seq[i]);
    assert(sub_i_plus_1.drop_last() =~= sub_i);
    
    if i == 0 {
        assert(sub_i_plus_1.len() == 1);
        assert(max_rcur(sub_i_plus_1) == sub_i_plus_1.first() as int);
    } else {
        assert(sub_i_plus_1.len() > 1);
        assert(max_rcur(sub_i_plus_1) == max(sub_i_plus_1.last() as int, max_rcur(sub_i_plus_1.drop_last())));
        assert(max_rcur(sub_i_plus_1) == max(seq[i] as int, max_rcur(sub_i)));
    }
}

/* code modified by LLM (iteration 3): added lemma to prove step-wise min property */
proof fn lemma_min_rcur_step(seq: Seq<i32>, i: int)
    requires 
        seq.len() > 0,
        1 <= i < seq.len(),
    ensures 
        min_rcur(seq.subrange(0, i + 1)) == min(seq[i] as int, min_rcur(seq.subrange(0, i))),
    decreases seq.len() - i
{
    let sub_i = seq.subrange(0, i);
    let sub_i_plus_1 = seq.subrange(0, i + 1);
    
    assert(sub_i_plus_1.len() == i + 1);
    assert(sub_i_plus_1.last() == seq[i]);
    assert(sub_i_plus_1.drop_last() =~= sub_i);
    
    if i == 0 {
        assert(sub_i_plus_1.len() == 1);
        assert(min_rcur(sub_i_plus_1) == sub_i_plus_1.first() as int);
    } else {
        assert(sub_i_plus_1.len() > 1);
        assert(min_rcur(sub_i_plus_1) == min(sub_i_plus_1.last() as int, min_rcur(sub_i_plus_1.drop_last())));
        assert(min_rcur(sub_i_plus_1) == min(seq[i] as int, min_rcur(sub_i)));
    }
}

/* code modified by LLM (iteration 1): added helper lemma to prove bounds on max_rcur */
proof fn lemma_max_rcur_bounds(seq: Seq<i32>)
    requires 
        seq.len() > 0,
        forall|i: int| 0 <= i < seq.len() ==> #[trigger] seq[i] > i32::MIN / 2 && #[trigger] seq[i] < i32::MAX / 2,
    ensures 
        i32::MIN / 2 < max_rcur(seq) < i32::MAX / 2,
    decreases seq.len()
{
    if seq.len() <= 1 {
        assert(max_rcur(seq) == seq.first() as int);
    } else {
        lemma_max_rcur_bounds(seq.drop_last());
        assert(max_rcur(seq) == max(seq.last() as int, max_rcur(seq.drop_last())));
    }
}

/* code modified by LLM (iteration 1): added helper lemma to prove bounds on min_rcur */
proof fn lemma_min_rcur_bounds(seq: Seq<i32>)
    requires 
        seq.len() > 0,
        forall|i: int| 0 <= i < seq.len() ==> #[trigger] seq[i] > i32::MIN / 2 && #[trigger] seq[i] < i32::MAX / 2,
    ensures 
        i32::MIN / 2 < min_rcur(seq) < i32::MAX / 2,
    decreases seq.len()
{
    if seq.len() <= 1 {
        assert(min_rcur(seq) == seq.first() as int);
    } else {
        lemma_min_rcur_bounds(seq.drop_last());
        assert(min_rcur(seq) == min(seq.last() as int, min_rcur(seq.drop_last())));
    }
}

//IMPL difference_max_min
/* code modified by LLM (iteration 3): fixed loop invariant maintenance using step lemmas */
fn difference_max_min(arr: &Vec<i32>) -> (diff: i32)
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> #[trigger] arr[i] > i32::MIN / 2 && #[trigger] arr[i] < i32::MAX / 2,
    ensures
        diff == max_rcur(arr@) - min_rcur(arr@),
{
    let mut max_val = arr[0];
    let mut min_val = arr[0];
    let mut i = 1;
    
    /* code modified by LLM (iteration 3): updated loop with proper invariant maintenance proofs */
    while i < arr.len()
        invariant
            1 <= i <= arr.len(),
            max_val == max_rcur(arr@.subrange(0, i as int)),
            min_val == min_rcur(arr@.subrange(0, i as int)),
        decreases arr.len() - i,
    {
        /* code modified by LLM (iteration 3): added proof before updates to establish step property */
        proof {
            lemma_max_rcur_step(arr@, i as int);
            lemma_min_rcur_step(arr@, i as int);
        }
        
        if arr[i] > max_val {
            max_val = arr[i];
            /* code modified by LLM (iteration 3): prove max_val update maintains invariant */
            proof {
                assert(max_val as int == arr[i] as int);
                assert(max_val as int == max(arr[i] as int, max_rcur(arr@.subrange(0, i as int))));
                assert(max_val as int == max_rcur(arr@.subrange(0, (i + 1) as int)));
            }
        } else {
            /* code modified by LLM (iteration 3): prove max_val invariant when no update */
            proof {
                assert(arr[i] <= max_val);
                assert(max_val as int == max_rcur(arr@.subrange(0, i as int)));
                assert(max_val as int >= arr[i] as int);
                assert(max_val as int == max(arr[i] as int, max_rcur(arr@.subrange(0, i as int))));
                assert(max_val as int == max_rcur(arr@.subrange(0, (i + 1) as int)));
            }
        }
        
        if arr[i] < min_val {
            min_val = arr[i];
            /* code modified by LLM (iteration 3): prove min_val update maintains invariant */
            proof {
                assert(min_val as int == arr[i] as int);
                assert(min_val as int == min(arr[i] as int, min_rcur(arr@.subrange(0, i as int))));
                assert(min_val as int == min_rcur(arr@.subrange(0, (i + 1) as int)));
            }
        } else {
            /* code modified by LLM (iteration 3): prove min_val invariant when no update */
            proof {
                assert(arr[i] >= min_val);
                assert(min_val as int == min_rcur(arr@.subrange(0, i as int)));
                assert(min_val as int <= arr[i] as int);
                assert(min_val as int == min(arr[i] as int, min_rcur(arr@.subrange(0, i as int))));
                assert(min_val as int == min_rcur(arr@.subrange(0, (i + 1) as int)));
            }
        }
        
        i += 1;
    }
    
    /* code modified by LLM (iteration 1): added proof that subrange equals full sequence and bounds checking */
    proof {
        lemma_max_rcur_subrange_full(arr@);
        lemma_min_rcur_subrange_full(arr@);
        lemma_max_rcur_bounds(arr@);
        lemma_min_rcur_bounds(arr@);
        
        assert(max_val == max_rcur(arr@.subrange(0, arr.len() as int)));
        assert(min_val == min_rcur(arr@.subrange(0, arr.len() as int)));
        assert(max_val == max_rcur(arr@));
        assert(min_val == min_rcur(arr@));
        
        // Prove no overflow
        assert(i32::MIN / 2 < max_rcur(arr@) < i32::MAX / 2);
        assert(i32::MIN / 2 < min_rcur(arr@) < i32::MAX / 2);
        assert(max_rcur(arr@) - min_rcur(arr@) > i32::MIN);
        assert(max_rcur(arr@) - min_rcur(arr@) < i32::MAX);
    }
    
    max_val - min_val
}

} // verus!