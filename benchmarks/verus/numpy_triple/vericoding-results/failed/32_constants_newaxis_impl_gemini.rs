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
    /* code modified by LLM (iteration 5): added decreases clause to prove loop termination */
    let ghost v_spec = v.view();
    let v_len = v.len();
    let mut v_mut = v;
    let mut result: Vec<Vec<T>> = Vec::new();

    let mut i: usize = 0;
    while i < v_len
        decreases v_len - i
        invariant
            i <= v_len,
            result.len() == i,
            v_mut.len() == v_len - i,
            v_mut.view() == v_spec.subrange(i as int, v_spec.len() as int),
            forall|j: int| 0 <= j < i as int ==> (
                result@.subrange(0, i as int)@[j].len() == 1 && result@.subrange(0, i as int)@[j][0] == v_spec[j]
            ),
    {
        let elem = v_mut.remove(0);
        proof {
            v_spec.subrange(i as int, v_spec.len() as int).subrange(1, v_spec.subrange(i as int, v_spec.len() as int).len()) === v_spec.subrange(i as int + 1, v_spec.len() as int);
        }
        let inner_vec = vec![elem];
        result.push(inner_vec);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}