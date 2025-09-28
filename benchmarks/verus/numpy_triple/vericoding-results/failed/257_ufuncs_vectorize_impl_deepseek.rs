// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

proof fn vectorize_lemma<A, B>(f: spec_fn(A) -> B, arr: Seq<A>, i: int)
    requires
        0 <= i <= arr.len(),
    ensures
        (arr.take(i).map(|j: int, a: A| f(a))).len() == i,
        forall|j: int| 0 <= j < i ==> arr.take(i).map(|j: int, a: A| f(a))[@j] == f(arr[@j])
    decreases i
{
    if i > 0 {
        vectorize_lemma(f, arr, i - 1);
    }
}

fn vec_map_helper<A, B>(f: spec_fn(A) -> B, arr: Vec<A>) -> (result: Vec<B>)
    ensures
        result.len() == arr.len(),
        forall|i: int| 0 <= i < arr.len() ==> result[i] == f(arr[i])
{
    let mut result = Vec::new();
    let mut index = 0;
    
    while index < arr.len()
        invariant
            result.len() == index,
            forall|j: int| 0 <= j < index ==> result[j] == f(arr[j]),
        decreases arr.len() - index
    {
        result.push(f(arr[index]));
        index = index + 1;
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
    /* code modified by LLM (iteration 5): Fixed parameter order in vectorize_lemma */
    vec_map_helper(f, arr)
}
// </vc-code>

}
fn main() {}