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

//IMPL difference_max_min
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
    
    /* code modified by LLM (iteration 1): added helper lemmas to establish relationship between iterative and recursive approaches */
    proof {
        assert(max_rcur(arr@.subrange(0, 1)) == arr[0] as int);
        assert(min_rcur(arr@.subrange(0, 1)) == arr[0] as int);
    }
    
    for i in 1..arr.len()
        invariant
            0 < arr.len(),
            /* code modified by LLM (iteration 1): fixed invariants to properly track max/min of prefix */
            max_val as int == max_rcur(arr@.subrange(0, i as int)),
            min_val as int == min_rcur(arr@.subrange(0, i as int)),
            forall|j: int| 0 <= j < arr.len() ==> i32::MIN / 2 < #[trigger] arr[j] < i32::MAX / 2,
    {
        /* code modified by LLM (iteration 1): added proof block to maintain invariant through updates */
        proof {
            let old_max = max_val;
            let old_min = min_val;
            let next_subrange = arr@.subrange(0, (i + 1) as int);
            let curr_subrange = arr@.subrange(0, i as int);
            
            assert(next_subrange == curr_subrange.push(arr[i]));
            assert(max_rcur(next_subrange) == max(arr[i] as int, max_rcur(curr_subrange)));
            assert(min_rcur(next_subrange) == min(arr[i] as int, min_rcur(curr_subrange)));
        }
        
        if arr[i] > max_val {
            max_val = arr[i];
        }
        if arr[i] < min_val {
            min_val = arr[i];
        }
    }
    
    /* code modified by LLM (iteration 1): added complete proof of bounds and postcondition */
    proof {
        assert(arr@.subrange(0, arr.len() as int) == arr@);
        
        let max_int = max_val as int;
        let min_int = min_val as int;
        
        // Establish bounds from precondition  
        assert(i32::MIN / 2 < max_val < i32::MAX / 2);
        assert(i32::MIN / 2 < min_val < i32::MAX / 2);
        
        // The difference is bounded
        let diff_int = max_int - min_int;
        assert(diff_int >= 0);
        assert(diff_int < (i32::MAX / 2) as int - (i32::MIN / 2) as int);
        assert(diff_int <= i32::MAX as int);
        assert(diff_int >= i32::MIN as int);
    }
    
    max_val - min_val
}

} // verus!

fn main() {}