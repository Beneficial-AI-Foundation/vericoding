// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_nonzero_skip(arr: Seq<f32>, i: nat)
    requires
        i < arr.len(),
    ensures
        nonzero_helper(arr.skip(i)) == nonzero_helper(arr.subrange(i, arr.len() as int)),
    decreases arr.len() - i
{
    if i == arr.len() - 1 {
        assert(arr.skip(i).len() == 1);
        assert(arr.subrange(i, arr.len() as int).len() == 1);
    } else {
        lemma_nonzero_skip(arr, i + 1);
    }
}

proof fn lemma_nonzero_relation(arr: Seq<f32>, i: nat)
    requires
        i < arr.len(),
    ensures
        nonzero_helper(arr.subrange(0, i + 1)) == 
            if arr[i] == 0.0f32 { 
                nonzero_helper(arr.subrange(0, i)) 
            } else { 
                nonzero_helper(arr.subrange(0, i)) + 1 
            },
    decreases i
{
    if i == 0 {
        assert(arr.subrange(0, 1).len() == 1);
        assert(arr.subrange(0, 0).len() == 0);
    } else {
        lemma_nonzero_relation(arr, i - 1);
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
    let mut count: usize = 0;
    let mut i: usize = 0;
    
    while i < arr.len()
        invariant
            i <= arr.len(),
            count <= i,
            count == nonzero_helper(arr@.subrange(0, i as int)),
        decreases arr.len() - i
    {
        if arr[i] != 0.0f32 {
            count = count + 1;
        }
        proof {
            lemma_nonzero_relation(arr@, i as nat);
        }
        i = i + 1;
    }
    
    assert(arr@.subrange(0, arr.len() as int) =~= arr@);
    count
}
// </vc-code>


}
fn main() {}