// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed incorrect helper and fixed syntax errors */
proof fn to_array_helper(xs: Seq<i32>, i: int) -> (result: Seq<i32>)
    requires
        0 <= i <= xs.len(),
    ensures
        result.len() == i,
        forall|j: int| 0 <= j < i ==> result[j] == xs[j],
{
    if i == 0 {
        Seq::empty()
    } else {
        let prev = to_array_helper(xs, i - 1);
        prev.push(xs[i - 1])
    }
}
// </vc-helpers>

// <vc-spec>
fn to_array(xs: &Seq<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == xs.len(),
        forall|i: int| 0 <= i < xs.len() ==> result[i] == xs[i],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed syntax error and improved ghost code usage */
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    
    proof {
        let ghost_result = to_array_helper(xs@, 0);
    }
    
    while i < xs.len() as usize
        invariant
            i <= xs.len() as usize,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == xs@[j],
        decreases (xs.len() as usize) - i
    {
        result.push(xs@[i as int]);
        i += 1;
        
        proof {
            let ghost_result = to_array_helper(xs@, i as int);
        }
    }
    result
}
// </vc-code>

}
fn main() {}