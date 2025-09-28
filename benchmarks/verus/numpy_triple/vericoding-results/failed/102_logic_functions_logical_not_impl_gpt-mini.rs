// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): len_sub_nonnegative for int indices */
fn len_sub_nonnegative_int<T>(x: &Vec<T>, i: int)
    requires
        0 <= i,
        i <= x.len(),
    ensures
        x.len() - i >= 0,
{
    proof {
        assert(0 <= i);
        assert(i <= x.len());
        assert(x.len() - i >= 0);
    }
}
// </vc-helpers>

// <vc-spec>
fn logical_not(x: Vec<f64>) -> (result: Vec<bool>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == (x[i] == 0.0)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterate with int index and use sequence indexing x@[i] */
    let mut result: Vec<bool> = Vec::new();
    let mut i: int = 0;
    while i < x.len()
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == (x@[j] == 0.0),
        decreases
            x.len() - i
    {
        result.push(x@[i] == 0.0);
        proof {
            assert(result.len() == i + 1);
            assert(result[i] == (x@[i] == 0.0));
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}