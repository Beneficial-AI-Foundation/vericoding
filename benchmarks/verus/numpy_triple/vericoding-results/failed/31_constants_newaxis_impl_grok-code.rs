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
/* code modified by LLM (iteration 5): Changed loop to use int for i, used v@.len() as loop bound, added #![auto] for triggers */{
    let len_nat = v@.len();
    let mut result: Vec<Vec<i8>> = Vec::new();
    let mut i: int = 0;
    while i < len_nat
        invariant
            result@.len() == i as int,
            forall|j: int| 0 <= j < i ==> #![auto] (
                result@[j].len() == 1 &&
                result@[j][0] == v@[j]
            )
        decreases len_nat - i
    {
        let val = v[i as usize];
        let mut inner: Vec<i8> = Vec::new();
        inner.push(val);
        result.push(inner);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}