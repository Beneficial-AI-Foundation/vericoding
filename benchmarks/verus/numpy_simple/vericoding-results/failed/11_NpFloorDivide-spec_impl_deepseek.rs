// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

proof fn lemma_div_result_bounds(a: i32, b: i32)
    requires b != 0,
    ensures (a / b) * b <= a,
            a < (a / b + 1) * b,
{
    assert(a / b <= a / b);
}

proof fn lemma_convert_vec_seq_indexing<T>(v: &Vec<T>, i: int)
    requires 0 <= i < v.len(),
    ensures v@[i] == v[i as usize],
{
    // Built-in axiom in Verus for vector indexing
}

proof fn lemma_convert_vec_seq_indexing_i8(v: &Vec<i8>, i: int)
    requires 0 <= i < v.len(),
    ensures v@[i] == v[i as usize] as int,
{
    lemma_convert_vec_seq_indexing(v, i);
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
{
    /* code modified by LLM (iteration 3): fix type conversion issues in indexing */
    let mut result = Vec::new();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] as i32 == (a@[j] as i32) / (b@[j] as i32),
        decreases a.len() - i,
    {
        let a_val = a[i];
        let b_val = b[i];
        
        proof {
            lemma_convert_vec_seq_indexing_i8(&a, i as int);
            lemma_convert_vec_seq_indexing_i8(&b, i as int);
            
            assert(is_non_zero_vector(a@.map(|i, x: i8| x as i32)));
            assert(a@.map(|i, x: i8| x as i32)[i as int] == a_val as i32);
            assert(a_val != 0);
            
            assert(is_non_zero_vector(b@.map(|i, x: i8| x as i32)));
            assert(b@.map(|i, x: i8| x as i32)[i as int] == b_val as i32);
            assert(b_val != 0);
        }
        
        let div_result = (a_val as i32) / (b_val as i32);
        result.push((div_result as i8));
        
        proof {
            lemma_convert_vec_seq_indexing_i8(&result, i as int);
            assert(result[i] == (div_result as i8));
            assert(result@[i as int] as i32 == div_result);
        }
        
        i = i + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}