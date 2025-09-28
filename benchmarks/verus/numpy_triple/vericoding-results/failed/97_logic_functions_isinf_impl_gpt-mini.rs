// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_infinite(x: f64) -> bool;
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): runtime wrapper for f64.is_infinite */
fn is_infinite_runtime(x: f64) -> bool { x.is_infinite() }

/* helper modified by LLM (iteration 5): proof that runtime equals spec */
fn is_infinite_runtime_equals_spec(x: f64)
    ensures
        is_infinite_runtime(x) == is_infinite(x),
{
    proof {
        assert(is_infinite_runtime(x) == x.is_infinite());
        assert(is_infinite(x) == x.is_infinite());
    }
}
// </vc-helpers>

// <vc-spec>
fn isinf(x: Vec<f64>) -> (result: Vec<bool>)
    requires x.len() < usize::MAX,
    ensures 
        result.len() == x.len(),
        forall|i: int| 0 <= i < x.len() ==> {
            result[i] == is_infinite(x@[i])
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement isinf by iterating with usize indices and proving spec relation */
    let n: usize = x.len();
    let mut result: Vec<bool> = Vec::new();
    let mut i: usize = 0;

    while i < n
        invariant
            i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> result[j] == is_infinite(x@[j]),
        decreases n - i
    {
        let xi: f64 = x[i];
        let b: bool = xi.is_infinite();
        proof {
            is_infinite_runtime_equals_spec(xi);
        }
        result.push(b);
        i = i + 1;
    }

    result
}
// </vc-code>

}
fn main() {}