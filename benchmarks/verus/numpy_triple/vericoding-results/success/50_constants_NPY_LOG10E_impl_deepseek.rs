// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec const LIBRARY_LOG10E: f64 = 0.434294481903251827651128918916605082;

proof fn log10e_is_constant()
    ensures
        LIBRARY_LOG10E == 0.434294481903251827651128918916605082,
{
}

/* helper modified by LLM (iteration 2): Ensure constant is accessible from exec mode */
const EXEC_LOG10E: f64 = 0.434294481903251827651128918916605082;
// </vc-helpers>

// <vc-spec>
fn npy_log10e() -> (result: f64)
    ensures
        result == 0.434294481903251827651128918916605082
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Use executable constant instead of spec constant */
    let result = EXEC_LOG10E;
    result
}
// </vc-code>


}
fn main() {}