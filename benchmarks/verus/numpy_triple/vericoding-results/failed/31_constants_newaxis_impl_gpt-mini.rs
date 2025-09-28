// <vc-preamble>
use vstd::prelude::*;

verus! {

pub enum NewAxis {
    Newaxis,
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): create single-element vector from i8 */
fn make_singleton(x: i8) -> (result: Vec<i8>)
    ensures
        result@.len() == 1,
        result@[0] == x,
{
    let mut row: Vec<i8> = Vec::new();
    row.push(x);
    row
}

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
    /* code modified by LLM (iteration 5): expand vector v into column vector using int indices */
    let mut result: Vec<Vec<i8>> = Vec::new();
    let mut i: int = 0;
    while i < v@.len()
        invariant
            result@.len() == i,
            0 <= i,
            i <= v@.len(),
            forall|j: int| 0 <= j && j < result@.len() ==> (
                result@[j].len() == 1 &&
                result@[j][0] == v@[j]
            ),
        decreases v@.len() - i
    {
        let x: i8 = v@[i];
        let row = make_singleton(x);
        result.push(row);
        i = i + 1;
    }
    result
}

// </vc-code>

}
fn main() {}