// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed incorrect lemma name */
proof fn lemma_nonzero_concat(s1: Seq<f32>, s2: Seq<f32>)
    ensures
        nonzero_helper(s1 + s2) == nonzero_helper(s1) + nonzero_helper(s2),
    decreases s1.len(),
{
    if s1.len() > 0 {
        vstd::seq_lib::lemma_seq_add_skip(s1, s2);
        lemma_nonzero_concat(s1.skip(1), s2);
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
{
    /* code modified by LLM (iteration 5): added subrange lemma and assertions to prove invariant */
    let mut count: usize = 0;
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            count <= i,
            count == nonzero_helper(arr@.subrange(0, i as int)),
        decreases arr.len() - i
    {
        if arr[i] != 0.0f32 {
            proof {
                vstd::seq_lib::lemma_subrange_succ(arr@, 0, i as int);
                let s1 = arr@.subrange(0, i as int);
                let s2 = seq![arr@[i as int]];
                lemma_nonzero_concat(s1, s2);
                assert(nonzero_helper(s2) == 1);
            }
            count = count + 1;
        } else {
            proof {
                vstd::seq_lib::lemma_subrange_succ(arr@, 0, i as int);
                let s1 = arr@.subrange(0, i as int);
                let s2 = seq![arr@[i as int]];
                lemma_nonzero_concat(s1, s2);
                assert(nonzero_helper(s2) == 0);
            }
        }
        i = i + 1;
    }
    count
}
// </vc-code>


}
fn main() {}