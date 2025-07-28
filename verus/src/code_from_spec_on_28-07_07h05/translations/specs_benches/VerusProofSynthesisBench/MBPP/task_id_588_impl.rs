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

/* code modified by LLM (iteration 1): added helper lemma to prove equivalence between subrange and full sequence */
proof fn lemma_max_min_full_seq(arr: Seq<i32>)
    requires arr.len() > 0
    ensures 
        max_rcur(arr.subrange(0, arr.len() as int)) == max_rcur(arr),
        min_rcur(arr.subrange(0, arr.len() as int)) == min_rcur(arr),
{
    assert(arr.subrange(0, arr.len() as int) =~= arr);
}

/* code modified by LLM (iteration 1): added helper lemma to prove max_rcur extension property */
proof fn lemma_max_rcur_extend(arr: Seq<i32>, i: int)
    requires 
        arr.len() > 0,
        1 <= i < arr.len(),
    ensures 
        max_rcur(arr.subrange(0, i + 1)) == max(arr[i] as int, max_rcur(arr.subrange(0, i))),
{
    let sub_i = arr.subrange(0, i);
    let sub_i_plus_1 = arr.subrange(0, i + 1);
    
    assert(sub_i_plus_1.drop_last() =~= sub_i);
    assert(sub_i_plus_1.last() == arr[i]);
}

/* code modified by LLM (iteration 1): added helper lemma to prove min_rcur extension property */
proof fn lemma_min_rcur_extend(arr: Seq<i32>, i: int)
    requires 
        arr.len() > 0,
        1 <= i < arr.len(),
    ensures 
        min_rcur(arr.subrange(0, i + 1)) == min(arr[i] as int, min_rcur(arr.subrange(0, i))),
{
    let sub_i = arr.subrange(0, i);
    let sub_i_plus_1 = arr.subrange(0, i + 1);
    
    assert(sub_i_plus_1.drop_last() =~= sub_i);
    assert(sub_i_plus_1.last() == arr[i]);
}

fn difference_max_min(arr: &Vec<i32>) -> (diff: i32)
    // pre-conditions-start
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < #[trigger] arr[i] < i32::MAX / 2,
    // pre-conditions-end
    // post-conditions-start
    ensures
        diff == max_rcur(arr@) - min_rcur(arr@),
    // post-conditions-end
{
    let mut max_val = arr[0];
    let mut min_val = arr[0];
    
    let mut i = 1;
    /* code modified by LLM (iteration 1): updated loop with proof annotations to maintain invariants */
    while i < arr.len()
        invariant
            1 <= i <= arr.len(),
            max_val == max_rcur(arr@.subrange(0, i as int)),
            min_val == min_rcur(arr@.subrange(0, i as int)),
            i32::MIN / 2 < max_val < i32::MAX / 2,
            i32::MIN / 2 < min_val < i32::MAX / 2,
        decreases arr.len() - i,
    {
        /* code modified by LLM (iteration 2): added proof before updates to establish extension properties */
        proof {
            lemma_max_rcur_extend(arr@, i as int);
            lemma_min_rcur_extend(arr@, i as int);
        }
        
        if arr[i] > max_val {
            max_val = arr[i];
            /* code modified by LLM (iteration 2): fixed type mismatch by using i as int for array access */
            proof {
                assert(max_val as int == max(arr[i as int] as int, max_rcur(arr@.subrange(0, i as int))));
                assert(max_val as int == max_rcur(arr@.subrange(0, (i + 1) as int)));
            }
        } else {
            /* code modified by LLM (iteration 2): fixed type mismatch by using i as int for array access */
            proof {
                assert(max_val as int == max_rcur(arr@.subrange(0, i as int)));
                assert(max_val as int >= arr[i as int] as int);
                assert(max_val as int == max(arr[i as int] as int, max_rcur(arr@.subrange(0, i as int))));
                assert(max_val as int == max_rcur(arr@.subrange(0, (i + 1) as int)));
            }
        }
        
        if arr[i] < min_val {
            min_val = arr[i];
            /* code modified by LLM (iteration 2): fixed type mismatch by using i as int for array access */
            proof {
                assert(min_val as int == min(arr[i as int] as int, min_rcur(arr@.subrange(0, i as int))));
                assert(min_val as int == min_rcur(arr@.subrange(0, (i + 1) as int)));
            }
        } else {
            /* code modified by LLM (iteration 2): fixed type mismatch by using i as int for array access */
            proof {
                assert(min_val as int == min_rcur(arr@.subrange(0, i as int)));
                assert(min_val as int <= arr[i as int] as int);
                assert(min_val as int == min(arr[i as int] as int, min_rcur(arr@.subrange(0, i as int))));
                assert(min_val as int == min_rcur(arr@.subrange(0, (i + 1) as int)));
            }
        }
        
        i += 1;
    }
    
    /* code modified by LLM (iteration 1): added proof that subrange equals full sequence and overflow check */
    proof {
        lemma_max_min_full_seq(arr@);
        assert(max_val == max_rcur(arr@));
        assert(min_val == min_rcur(arr@));
        // Overflow check: since both values are in range [MIN/2+1, MAX/2-1],
        // their difference is in range [MIN+2, MAX-2], which fits in i32
        assert(max_val - min_val >= i32::MIN && max_val - min_val <= i32::MAX);
    }
    
    max_val - min_val
}

} // verus!

fn main() {}