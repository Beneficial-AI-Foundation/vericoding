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
    /* code modified by LLM (iteration 5): Added proof block to help verify invariant preservation */
    let mut result: Vec<Vec<i8>> = Vec::new();
    let mut i: usize = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            result@.len() == i as int,
            forall|j: int| 0 <= j < i as int ==> result@[j].len() == 1,
            forall|j: int| 0 <= j < i as int ==> result@[j][0] == v@[j],
        decreases v.len() - i
    {
        let mut inner: Vec<i8> = Vec::new();
        inner.push(v[i]);
        
        let old_result = result;
        result.push(inner);
        
        proof {
            assert(result@.len() == (i + 1) as int);
            assert(result@[i as int].len() == 1);
            assert(result@[i as int][0] == v@[i as int]);
            assert(forall|j: int| 0 <= j < i as int ==> result@[j] == old_result@[j]);
            assert(forall|j: int| 0 <= j < i as int ==> old_result@[j].len() == 1);
            assert(forall|j: int| 0 <= j < i as int ==> old_result@[j][0] == v@[j]);
            assert(forall|j: int| 0 <= j < (i + 1) as int ==> result@[j].len() == 1);
            assert(forall|j: int| 0 <= j < (i + 1) as int ==> result@[j][0] == v@[j]);
        }
        
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}