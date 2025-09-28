// <vc-preamble>
use vstd::prelude::*;

verus! {

pub enum NewAxis {
    Newaxis,
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed predicate syntax */
predicate is_column_of(v: Vec<Vec<i8>>, col: Vec<i8>) -> bool {
    v@.len() == col@.len() &&
    forall|i: int| 0 <= i < v@.len() ==> (
        v@[i].len() == 1 &&
        v@[i][0] == col@[i]
    )
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
/* code modified by LLM (iteration 5): Fixed predicate call syntax */
{
    let mut result: Vec<Vec<i8>> = Vec::new();
    let mut i: usize = 0;
    let n = v.len();
    while i < n
        invariant
            0 <= i <= n,
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> (
                result@[j]@.len() == 1 &&
                result@[j][0] == v@[j]
            ),
        decreases n - i
    {
        let mut row: Vec<i8> = Vec::new();
        proof {
            assert(v.index(i) == v@[i]) by (auto);
        }
        row.push(v[i]);
        result.push(row);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}