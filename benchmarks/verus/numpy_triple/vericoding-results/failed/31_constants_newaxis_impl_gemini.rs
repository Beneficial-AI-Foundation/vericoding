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
fn expand_to_column(v: Vec<i8>, axis: NewAxis) -> (result: Vec<Vec<i8>>)
    ensures
        result@.len() == v@.len(),
        forall|i: int| 0 <= i < result@.len() ==> (
            result@[i].len() == 1 &&
            result@[i][0] == v@[i]
        ),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): removed incorrect, nonexistent lemma call */
    let mut result: Vec<Vec<i8>> = Vec::new();
    let mut i: usize = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            result@.len() == i as int,
            forall|j: int| 0 <= j < i as int ==> (
                result@[j]@.len() == 1 &&
                result@[j]@[0] == v@[j]
            ),
        decreases v.len() - i
    {
        let element = v[i];
        let new_row = vec![element];
        
        result.push(new_row);

        proof {
            assert(new_row@.len() == 1 && new_row@[0] == v@[i as int]);
        }
        
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}