// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn npy_log10e() -> (result: f64)
    ensures
        result == 0.434294481903251827651128918916605082
// </vc-spec>
// <vc-code>
{
    0.434294481903251827651128918916605082
}
// </vc-code>


}
fn main() {}