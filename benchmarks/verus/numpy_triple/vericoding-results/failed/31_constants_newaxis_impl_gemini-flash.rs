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
    let mut result: Vec<Vec<i8>> = Vec::new();
    let mut i: int = 0;
    while i < v.len()
        invariant
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> (result@[j].len() == 1 && result@[j][0] == v@[j]),
            i <= v.len(),
        decreases v.len() - i
    {
        let mut inner_vec: Vec<i8> = Vec::new();
        inner_vec.push(v[i as usize]);
        result.push(inner_vec);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}