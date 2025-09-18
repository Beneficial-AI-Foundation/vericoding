// <vc-preamble>
use vstd::prelude::*;

verus! {

pub enum NewAxis {
    Newaxis,
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn expand_to_column<T>(v: Vec<T>, axis: NewAxis) -> (result: Vec<Vec<T>>)
    ensures
        result.len() == v.len(),
        forall|i: int| 0 <= i < result.len() ==> (
            result[i].len() == 1 &&
            result[i][0] == v[i]
        ),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Using into_iter() to consume vector and avoid borrowing issues */
    let mut result: Vec<Vec<T>> = Vec::new();
    let mut temp_vec: Vec<T> = Vec::new();
    
    // Move all elements from v into temp_vec
    let mut i = 0;
    while i < v.len()
        invariant
            i <= v.len(),
            temp_vec.len() == i,
            forall|j: int| 0 <= j < i ==> temp_vec[j] == v[j],
    {
        temp_vec.push(v.into_iter().nth(0).unwrap());
        i += 1;
    }
    
    // Now create the result
    let mut j = 0;
    while j < temp_vec.len()
        invariant
            j <= temp_vec.len(),
            result.len() == j,
            temp_vec.len() == v.len(),
            forall|k: int| 0 <= k < j ==> (
                result[k].len() == 1 &&
                result[k][0] == temp_vec[k]
            ),
            forall|k: int| 0 <= k < temp_vec.len() ==> temp_vec[k] == v[k],
    {
        let mut inner = Vec::new();
        inner.push(temp_vec.into_iter().nth(0).unwrap());
        result.push(inner);
        j += 1;
    }
    result
}
// </vc-code>

}
fn main() {}