use vstd::prelude::*;

verus! {

// <vc-helpers>
// No changes needed for helpers in this case
// </vc-helpers>

// <vc-spec>
// <vc-spec>
spec fn pi_approx() -> int { 314159265358979323846i128 as int }
spec fn scale_factor() -> int { 100000000000000000000i128 as int }

fn degrees_to_radians(degrees: i64) -> (radians: i64)
    ensures radians as int == (degrees as int * pi_approx()) / scale_factor() / 180
// </vc-spec>
// </vc-spec>

// <vc-code>
fn degrees_to_radians(degrees: i64) -> (radians: i64)
    ensures radians as int == (degrees as int * pi_approx()) / scale_factor() / 180
{
    let pi = 314159265358979323846i128;
    let scale = 100000000000000000000i128;
    let result = (degrees as i128 * pi) / scale / 180;
    result as i64
}
// </vc-code>

fn main() {
}

}