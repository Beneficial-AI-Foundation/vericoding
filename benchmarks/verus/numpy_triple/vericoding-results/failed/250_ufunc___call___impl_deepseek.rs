// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

proof fn lemma_vec_index_valid<T>(v: &Vec<T>, i: int)
    requires 0 <= i < v@.len()
    ensures v[i] == v@[i]
{
    assert(v@.index(i) == v@[i]);
}

proof fn lemma_vec_push_valid<T>(v: &mut Vec<T>, val: T)
    ensures v@.len() == old(v)@.len() + 1,
        forall|j: int| 0 <= j < old(v)@.len() ==> v@[j] == old(v)@[j],
        v@[old(v)@.len()] == val
{
}

spec fn spec_op_wrapper(op: spec_fn(f32, f32) -> f32, x: f32, y: f32) -> f32 {
    op(x, y)
}

// </vc-helpers>

// <vc-spec>
fn ufunc_call(op: spec_fn(f32, f32) -> f32, a: &Vec<f32>, b: &Vec<f32>) -> (result: Vec<f32>)
    requires a@.len() == b@.len(),
    ensures 
        result@.len() == a@.len(),
        forall|i: int| 0 <= i < result@.len() ==> result@[i] == op(a@[i], b@[i])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed type casting and indexing issues */
    let mut result = Vec::new();
    let len: int = a@.len() as int;
    let mut idx: int = 0;
    
    while idx < len
        invariant
            0 <= idx <= len,
            result@.len() == idx,
            forall|i: int| 0 <= i < idx ==> result@[i] == op(a@[i], b@[i])
        decreases len - idx
    {
        let a_val = a[idx as usize];
        let b_val = b[idx as usize];
        let res_val = op(a_val, b_val);
        
        result.push(res_val);
        
        proof {
            lemma_vec_push_valid(&mut result, res_val);
        }
        
        idx = idx + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}