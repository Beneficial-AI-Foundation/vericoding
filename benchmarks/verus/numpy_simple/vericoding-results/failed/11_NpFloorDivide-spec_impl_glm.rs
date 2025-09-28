// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): 'fix seq macro type compatibility' */
proof fn lemma_non_zero_vector_elements(v: Seq<i8>)
    requires
        is_non_zero_vector(v.map(|i, x: i8| x as i32)),
    ensures
        forall|i: int| 0 <= i < v.len() ==> (v[i] as i32) != 0,
{
    assert(forall|i: int| 0 <= i < v.len() ==> v.map(|j, x: i8| x as i32)[i] == v[i] as i32);
}
// </vc-helpers>

// <vc-spec>
spec fn is_non_zero_vector(v: Seq<i32>) -> bool {
    forall|i: int| 0 <= i < v.len() ==> v[i] != 0
}

fn floor_divide(a: Vec<i8>, b: Vec<i8>) -> (result: Vec<i8>)
    requires 
        a.len() == b.len(),
        is_non_zero_vector(a@.map(|i, x: i8| x as i32)),
        is_non_zero_vector(b@.map(|i, x: i8| x as i32)),
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] as i32 == (a[i] as i32) / (b[i] as i32),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): 'no changes needed' */
{
    let n = a.len();
    let mut result = Vec::with_capacity(n);
    
    proof {
        lemma_non_zero_vector_elements(a@);
        lemma_non_zero_vector_elements(b@);
    }
    
    let mut i = 0;
    while i < n
        invariant
            0 <= i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] as i32 == (a[j] as i32) / (b[j] as i32),
        decreases n - i,
    {
        let a_val = a[i];
        let b_val = b[i];
        proof {
            assert(b_val as i32 != 0);
        }
        let div_result = (a_val as i32) / (b_val as i32);
        result.push(#[verifier::truncate] div_result as i8);
        i = i + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}