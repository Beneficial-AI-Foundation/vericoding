// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn vectorize_helper<A, B>(f: spec_fn(A) -> B, arr: Vec<A>) -> (result: Vec<B>)
    ensures
        result.len() == arr.len(),
        forall|i: int| 0 <= i < arr.len() ==> result[i] == f(arr[i])
{
    let mut result = Vec::new();
    let mut n: usize = 0;
    
    while n < arr.len()
        invariant
            0 <= n <= arr.len(),
            result.len() == n,
            forall|i: int| 0 <= i < n ==> result[i] == f(arr[i])
        decreases arr.len() - n
    {
        result.push(f(arr[n as int]));
        n = n + 1;
    }
    
    result
}
// </vc-helpers>

// <vc-spec>
fn vectorize<A, B>(f: spec_fn(A) -> B, arr: Vec<A>) -> (result: Vec<B>)
    ensures
        result.len() == arr.len(),
        forall|i: int| 0 <= i < arr.len() ==> result[i] == f(arr[i])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed type mismatches with proper usize/int casting */
    let mut result = Vec::new();
    let mut i: usize = 0;
    
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == f(arr[j])
        decreases arr.len() - i
    {
        let value = f(arr[i as int]);
        result.push(value);
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}