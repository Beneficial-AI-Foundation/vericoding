// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Ensure proper index bounds and arithmetic safety */
fn lemma_vec_index_in_bounds(vec: &Vec<i8>, idx: usize)
    requires 0 <= idx < vec.len()
    ensures idx < vec.view().len()
{
    proof {
        assert(vec.view().len() == vec.len());
    }
}

fn lemma_safe_subtraction(x1_val: i8, x2_val: i8) 
    ensures x1_val - x2_val == -(x2_val - x1_val)
{
    proof {
        assert(x1_val - x2_val == -(x2_val - x1_val));
    }
}

fn lemma_subtract_zero_preserves(x_val: i8) 
    ensures x_val - 0 == x_val
{
    proof {
        assert(x_val - 0 == x_val);
    }
}

fn lemma_subtract_self_zero(x_val: i8) 
    ensures x_val - x_val == 0
{
    proof {
        assert(x_val - x_val == 0);
    }
}
// </vc-helpers>

// <vc-spec>
fn subtract(x1: Vec<i8>, x2: Vec<i8>) -> (result: Vec<i8>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result@[i] == x1@[i] - x2@[i],
        /* Sanity check: subtracting zero preserves the original value */
        forall|i: int| 0 <= i < result.len() && x2@[i] == 0 ==> result@[i] == x1@[i],
        /* Sanity check: subtracting a value from itself yields zero */
        forall|i: int| 0 <= i < result.len() && x1@[i] == x2@[i] ==> result@[i] == 0,
        /* Anti-commutativity property */
        forall|i: int| 0 <= i < result.len() ==> result@[i] == -(x2@[i] - x1@[i])
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fix loop invariant and add proper sequence bounds checking */
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    let len = x1.len();
    
    while i < len
        invariant
            i <= len,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> 0 <= j < x1.len() && 0 <= j < x2.len() && result@[j] == x1@[j] - x2@[j],
        decreases len - i
    {
        lemma_vec_index_in_bounds(&x1, i);
        lemma_vec_index_in_bounds(&x2, i);
        
        let x1_val = x1[i];
        let x2_val = x2[i];
        let diff = x1_val - x2_val;
        result.push(diff);
        i = i + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}