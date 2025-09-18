// <vc-preamble>
use vstd::prelude::*;

verus! {

pub enum NewAxis {
    Newaxis,
}
// </vc-preamble>

// <vc-helpers>
fn expand_to_column_helper<T: Clone>(v: Vec<T>, i: usize) -> (result: Vec<T>)
    requires
        0 <= i < v.len(),
    ensures
        result.len() == 1,
        result[0] == v@[i],
{
    let mut res = Vec::new();
    res.push(v[i]);
    res
}

/* helper modified by LLM (iteration 5): Fixed sequence indexing syntax */
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
    /* code modified by LLM (iteration 5): Added Clone bound to function signature */
    let mut result: Vec<Vec<T>> = Vec::new();
    let mut i: usize = 0;
    while i < v.len()
        invariant
            i <= v.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> (
                result[j].len() == 1 &&
                result[j]@[0] == v@[j]
            ),
    {
        let row = expand_to_column_helper(v.clone(), i);
        result.push(row);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}