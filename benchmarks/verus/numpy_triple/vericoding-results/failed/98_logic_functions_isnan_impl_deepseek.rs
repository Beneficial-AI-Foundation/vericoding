// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

/* helper modified by LLM (iteration 5): Make helper functions spec_fn for ghost code compatibility */
#[spec]
fn is_nan_f64(x: f64) -> (b: bool)
    ensures b == true <==> x != x,
{
    if x != x {
        true
    } else {
        false
    }
}

#[spec]
fn vec_map_f64_bool(v: Vec<f64>, f: impl Fn(f64) -> bool) -> (result: Vec<bool>)
    ensures
        result@.len() == v@.len(),
        forall|i: int| 0 <= i < v@.len() ==> result@[i] == f(v@[i]),
{
    let mut result = Vec::new();
    let mut i = 0;
    while i < v.len()
        invariant
            0 <= i <= v@.len(),
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == f(v@[j]),
    {
        result.push(f(v[i]));
        i += 1;
    }
    result
}

// </vc-helpers>

// <vc-spec>
fn isnan(x: Vec<f64>) -> (result: Vec<bool>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < x@.len() ==> (result[i] == true <==> x[i] != x[i]),
        forall|i: int| 0 <= i < x@.len() ==> (result[i] == true ==> x[i] != x[i]),
        forall|i: int| 0 <= i < x@.len() ==> (x[i] == x[i] ==> result[i] == false),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Use ghost code compatible implementation with closure */
    let mut result = Vec::new();
    let mut i = 0;
    while i < x.len()
        invariant
            0 <= i <= x@.len(),
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == (x@[j] != x@[j]),
    {
        result.push(x[i] != x[i]);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}