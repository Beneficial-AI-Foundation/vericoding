// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): relate Vec seq length to len */
fn vec_seq_len<T>(v: &Vec<T>)
    ensures
        v@.len() == v.len() as int,
{
    proof {
        assert(v@.len() == v.len() as int);
    }
}

// </vc-helpers>

// <vc-spec>
fn numpy_reciprocal(x: Vec<f32>) -> (result: Vec<f32>)
    requires 
        x.len() > 0,
        forall|i: int| 0 <= i < x@.len() ==> x@[i] != 0.0f32,
    ensures
        result@.len() == x@.len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use usize index and decrease on seq length difference */
    let mut result = Vec::<f32>::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            result@.len() == i as int,
        decreases x@.len() - result@.len()
    {
        proof {
            vec_seq_len(&x);
            assert((i as int) < x@.len());
        }
        let xi: f32 = x[i];
        proof {
            assert(x@[i as int] != 0.0f32);
        }
        let r: f32 = 1.0f32 / xi;
        result.push(r);
        i = i + 1;
    }
    result
}

// </vc-code>

}
fn main() {}