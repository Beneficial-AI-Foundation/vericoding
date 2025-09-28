// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): named return with exact constant */
fn get_log10e() -> (result: f64)
    ensures
        result == 0.434294481903251827651128918916605082,
{
    0.434294481903251827651128918916605082_f64
}
// </vc-helpers>

// <vc-spec>
fn npy_log10e() -> (result: f64)
    ensures
        result == 0.434294481903251827651128918916605082
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): use helper get_log10e to compute result */
{
    /* code modified by LLM (iteration 2): return the constant from helper */
    let result: f64 = get_log10e();
    result
}
// </vc-code>


}
fn main() {}