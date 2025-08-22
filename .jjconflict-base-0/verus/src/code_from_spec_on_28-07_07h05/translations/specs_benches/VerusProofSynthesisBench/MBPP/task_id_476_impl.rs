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

/* code modified by LLM (iteration 1): Added helper lemmas to prove correctness of max/min updates */
proof fn lemma_max_rcur_extend(arr: Seq<i32>, i: int)
    requires 
        arr.len() > 0,
        0 < i < arr.len(),
    ensures 
        max_rcur(arr.subrange(0, i + 1)) == max(arr[i] as int, max_rcur(arr.subrange(0, i)))
{
    let sub_i = arr.subrange(0, i);
    let sub_i_plus_1 = arr.subrange(0, i + 1);
    
    assert(sub_i_plus_1.len() == i + 1);
    assert(sub_i_plus_1.last() == arr[i]);
    assert(sub_i_plus_1.drop_last() =~= sub_i);
}

proof fn lemma_min_rcur_extend(arr: Seq<i32>, i: int)
    requires 
        arr.len() > 0,
        0 < i < arr.len(),
    ensures 
        min_rcur(arr.subrange(0, i + 1)) == min(arr[i] as int, min_rcur(arr.subrange(0, i)))
{
    let sub_i = arr.subrange(0, i);
    let sub_i_plus_1 = arr.subrange(0, i + 1);
    
    assert(sub_i_plus_1.len() == i + 1);
    assert(sub_i_plus_1.last() == arr[i]);
    assert(sub_i_plus_1.drop_last() =~= sub_i);
}

proof fn lemma_max_rcur_subrange_equiv(arr: Seq<i32>)
    requires arr.len() > 0
    ensures max_rcur(arr.subrange(0, arr.len() as int)) == max_rcur(arr)
{
    assert(arr.subrange(0, arr.len() as int) =~= arr);
}

proof fn lemma_min_rcur_subrange_equiv(arr: Seq<i32>)
    requires arr.len() > 0
    ensures min_rcur(arr.subrange(0, arr.len() as int)) == min_rcur(arr)
{
    assert(arr.subrange(0, arr.len() as int) =~= arr);
}

//IMPL sum_min_max
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
    
    /* code modified by LLM (iteration 2): Fixed type mismatches by using int indexing in proof blocks */
    for i in 1..arr.len()
        invariant
            0 < i <= arr.len(),
            max_val == max_rcur(arr@.subrange(0, i as int)),
            min_val == min_rcur(arr@.subrange(0, i as int)),
            i32::MIN / 2 < max_val < i32::MAX / 2,
            i32::MIN / 2 < min_val < i32::MAX / 2,
    {
        proof {
            lemma_max_rcur_extend(arr@, i as int);
            lemma_min_rcur_extend(arr@, i as int);
        }
        
        if arr[i] > max_val {
            max_val = arr[i];
            proof {
                assert(max_val as int == max(arr[i as int] as int, max_rcur(arr@.subrange(0, i as int))));
                assert(max_val as int == max_rcur(arr@.subrange(0, (i + 1) as int)));
            }
        } else {
            proof {
                assert(max_val as int == max_rcur(arr@.subrange(0, i as int)));
                assert(max_val as int >= arr[i as int] as int);
                assert(max_val as int == max(arr[i as int] as int, max_rcur(arr@.subrange(0, i as int))));
                assert(max_val as int == max_rcur(arr@.subrange(0, (i + 1) as int)));
            }
        }
        
        if arr[i] < min_val {
            min_val = arr[i];
            proof {
                assert(min_val as int == min(arr[i as int] as int, min_rcur(arr@.subrange(0, i as int))));
                assert(min_val as int == min_rcur(arr@.subrange(0, (i + 1) as int)));
            }
        } else {
            proof {
                assert(min_val as int == min_rcur(arr@.subrange(0, i as int)));
                assert(min_val as int <= arr[i as int] as int);
                assert(min_val as int == min(arr[i as int] as int, min_rcur(arr@.subrange(0, i as int))));
                assert(min_val as int == min_rcur(arr@.subrange(0, (i + 1) as int)));
            }
        }
    }
    
    /* code modified by LLM (iteration 1): Added proof block to establish postcondition */
    proof {
        lemma_max_rcur_subrange_equiv(arr@);
        lemma_min_rcur_subrange_equiv(arr@);
        assert(max_val == max_rcur(arr@));
        assert(min_val == min_rcur(arr@));
    }
    
    max_val + min_val
}

} // verus!

fn main() {}