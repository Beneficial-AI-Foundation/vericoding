// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed type mismatch in tail helper and proof */
spec fn nonzero_helper_tail(seq: Seq<f32>, count: nat) -> nat 
    decreases seq.len()
{
    if seq.len() == 0 {
        count
    } else {
        let next_count = if seq[0] == 0.0f32 { count } else { count + 1 };
        nonzero_helper_tail(seq.skip(1), next_count)
    }
}

proof fn nonzero_helper_equiv(seq: Seq<f32>)
    ensures
        nonzero_helper(seq) == nonzero_helper_tail(seq, 0),
    decreases seq.len()
{
    if seq.len() == 0 {
    } else {
        nonzero_helper_equiv(seq.skip(1));
        assert(nonzero_helper(seq) == (if seq[0] == 0.0f32 { nonzero_helper(seq.skip(1)) } else { nonzero_helper(seq.skip(1)) + 1 }));
        assert(nonzero_helper_tail(seq, 0) == nonzero_helper_tail(seq.skip(1), if seq[0] == 0.0f32 { 0 } else { 1 }));
        assert(nonzero_helper(seq.skip(1)) == nonzero_helper_tail(seq.skip(1), 0));
    }
}
// </vc-helpers>

// <vc-spec>
spec fn nonzero_helper(arr: Seq<f32>) -> nat 
    decreases arr.len()
{
    if arr.len() == 0 {
        0
    } else {
        let rest_count = nonzero_helper(arr.skip(1));
        if arr[0] == 0.0f32 {
            rest_count
        } else {
            rest_count + 1
        }
    }
}

fn nonzero(arr: Vec<f32>) -> (result: usize)
    ensures 
        result <= arr.len(),
        result == nonzero_helper(arr@),
        arr.len() > 0 && arr[0] == 0.0f32 ==> 
            nonzero_helper(arr@.skip(1)) == if result > 0 { result - 1 } else { 0 }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed type conversion issue in proof assertion */
{
    let mut i: usize = 0;
    let mut count: usize = 0;
    
    while i < arr.len()
        invariant
            i <= arr.len(),
            count == nonzero_helper_tail(arr@.take(i as int), 0),
            count <= i,
        decreases arr.len() - i
    {
        let current_val = arr[i];
        let prev_count = count;
        
        if current_val != 0.0f32 {
            count = count + 1;
        }
        
        proof {
            let seq_i = arr@.take(i as int);
            let seq_i1 = arr@.take((i + 1) as int);
            assert(seq_i1.skip(i as int).len() == 1);
            assert(seq_i1 == seq_i.push(current_val));
            
            nonzero_helper_equiv(seq_i1.skip(i as int));
            assert(nonzero_helper_tail(seq_i1.skip(i as int), 0) == if current_val == 0.0f32 { 0 } else { 1 });
            assert(nonzero_helper_tail(seq_i1, 0) == nonzero_helper_tail(seq_i, nonzero_helper_tail(seq_i1.skip(i as int), 0)));
            assert(nonzero_helper_tail(seq_i1, 0) == nonzero_helper_tail(seq_i, if current_val == 0.0f32 { 0 } else { 1 }));
            assert(nonzero_helper_tail(seq_i1, 0) == if current_val == 0.0f32 { prev_count as nat } else { prev_count as nat + 1 });
        }
        
        i = i + 1;
    }
    
    proof {
        nonzero_helper_equiv(arr@);
        assert(arr@.take(arr.len() as int) == arr@);
    }
    
    count
}
// </vc-code>


}
fn main() {}