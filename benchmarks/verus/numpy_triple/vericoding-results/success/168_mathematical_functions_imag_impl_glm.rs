// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn imag(val: Vec<(f64, f64)>) -> (result: Vec<f64>)
    ensures
        result.len() == val.len(),
        forall|i: int| 0 <= i < val.len() ==> result[i as int] == val[i as int].1,
        forall|i: int| 0 <= i < val.len() ==> (val[i as int].1 == 0.0 ==> result[i as int] == 0.0),
        forall|i: int| 0 <= i < val.len() ==> (val[i as int].0 != 0.0 || val[i as int].1 != 0.0 ==> result[i as int] == val[i as int].1),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fixed precondition by adding val.len() == n to invariant */
    let n = val.len();
    let mut result = Vec::new();
    result.resize(n, 0.0);
    let mut i = 0;
    while i < n
        invariant
            0 <= i <= n,
            val.len() == n,
            result.len() == n,
            forall|j: int| 0 <= j < i ==> result[j] == val[j].1,
        decreases n - i
    {
        result.set(i, val[i].1);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}