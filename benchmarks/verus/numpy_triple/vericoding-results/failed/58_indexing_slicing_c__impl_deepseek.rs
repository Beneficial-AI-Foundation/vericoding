// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn vec_index_same<T>(v: Vec<T>, i: int)
    requires 0 <= i < v.len()
    ensures v@[i] == v[i]
{
}

proof fn vec_clone_index_same<T>(v: Vec<T>, i: int)
    requires 0 <= i < v.len()
    ensures v.clone()@[i] == v@[i]
{
    vec_index_same(v.clone(), i);
}

/* helper modified by LLM (iteration 5): Maintain proof helpers for vector indexing correctness */
// </vc-helpers>

// <vc-spec>
fn c_(arr1: Vec<i8>, arr2: Vec<i8>) -> (result: Vec<Vec<i8>>)
    requires arr1.len() == arr2.len(),
    ensures 
        result.len() == arr1.len(),
        forall|i: int| 0 <= i < result.len() ==> 
            result[i]@.len() == 2 &&
            result[i][0] == arr1[i] &&
            result[i][1] == arr2[i]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fix variable name in loop invariant from 'n' to 'i' */
    let len = arr1.len();
    let mut result: Vec<Vec<i8>> = Vec::new();
    
    let mut n: usize = 0;
    while n < len
        invariant
            n <= len,
            result@.len() == n as nat,
            forall|i: int| 0 <= i < n ==> 
                result@[i]@.len() == 2,
                result@[i][0] == arr1@[i],
                result@[i][1] == arr2@[i]
        decreases len - n
    {
        let mut inner_vec = Vec::new();
        inner_vec.push(arr1[n]);
        inner_vec.push(arr2[n]);
        
        proof {
            vec_clone_index_same(arr1, n);
            vec_clone_index_same(arr2, n);
        }
        
        result.push(inner_vec);
        n = n + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}