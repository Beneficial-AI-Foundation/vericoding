use vstd::prelude::*;

verus! {

// <vc-helpers>
exec const PI_APPROX: i128 = 314159265358979323846i128;

exec const SCALE_FACTOR: i128 = 100000000000000000000i128;
// </vc-helpers>

// <vc-spec>
spec fn pi_approx() -> int { 314159265358979323846i128 as int }
spec fn scale_factor() -> int { 100000000000000000000i128 as int }

fn degrees_to_radians(degrees: i64) -> (radians: i64)
    ensures radians as int == (degrees as int * pi_approx()) / scale_factor() / 180
// </vc-spec>
// <vc-code>
{
    let num = degrees as i128 * PI_APPROX;
    let den1 = SCALE_FACTOR;
    let den2 = 180i128;
    let result = num / den1 / den2;
    proof {
        assert(result as int == (degrees as int * pi_approx()) / scale_factor() / 180);
    }
    result as i64
}
// </vc-code>

fn main() {
}

}