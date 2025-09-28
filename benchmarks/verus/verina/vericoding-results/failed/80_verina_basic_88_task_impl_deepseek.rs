// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed ghost type parameters and simplified helper functions */
pub proof fn lemma_vec_push_preserves_elems(vec: &mut Vec<i32>, len: usize, x: i32)
    ensures
        vec.len() == old(vec).len() + 1,
        forall|j: int| 0 <= j < old(vec).len() as int ==> vec[j as usize] == old(vec)[j as usize],
        vec[old(vec).len()] == x,
{
    // Built-in lemma
}

pub proof fn lemma_vec_init_empty() -> (vec: Vec<i32>)
    ensures
        vec.len() == 0,
{
    Vec::new()
}
// </vc-helpers>

// <vc-spec>
fn to_array(xs: &Seq<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == xs.len(),
        forall|i: int| 0 <= i < xs.len() ==> result[i] == xs[i],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed compilation error by using usize indexing */
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    
    while i < xs.len() as usize
        invariant
            i <= xs.len() as usize,
            result.len() == i,
            forall|j: usize| j < i ==> result[j] == xs[j as int],
    {
        result.push(xs[i as int]);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}