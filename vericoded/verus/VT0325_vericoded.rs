// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): monotonicity of usize->int cast for < */
proof fn lemma_usize_lt_to_int_lt(a: usize, b: usize)
    requires
        a < b,
    ensures
        (a as int) < (b as int),
{
    assert((a as int) < (b as int));
}

/* helper modified by LLM (iteration 5): monotonicity of usize->int cast for <= */
proof fn lemma_usize_le_to_int_le(a: usize, b: usize)
    requires
        a <= b,
    ensures
        (a as int) <= (b as int),
{
    assert((a as int) <= (b as int));
}
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
    /* code modified by LLM (iteration 5): build result by iterating and pushing imaginary parts; fixed invariants and avoided unnecessary proof */
    let mut result: Vec<f64> = Vec::new();
    let n: usize = val.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == val.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> result[j as int] == val[j as int].1,
        decreases (n - i) as int
    {
        let im = val[i].1;
        result.push(im);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}