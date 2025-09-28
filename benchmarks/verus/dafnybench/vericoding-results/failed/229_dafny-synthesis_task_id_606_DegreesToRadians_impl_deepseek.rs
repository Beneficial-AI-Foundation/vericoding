use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn pi_approx_scaled() -> int {
    pi_approx() / scale_factor()
}

proof fn lemma_scaling() 
    ensures
        forall|deg: int| 
            deg * pi_approx() / scale_factor() / 180 == deg * pi_approx_scaled() / 180,
{
    assert forall|deg: int| deg * pi_approx() / scale_factor() / 180 == deg * pi_approx_scaled() / 180 by {
        assert(pi_approx_scaled() == pi_approx() / scale_factor());
    };
}

spec fn to_i64(x: int) -> i64
    recommends -9223372036854775808 <= x <= 9223372036854775807
{
    x as i64
}

spec fn compute_scaled_pi_int() -> int {
    pi_approx() / scale_factor()
}
// </vc-helpers>

// <vc-spec>
spec fn pi_approx() -> int { 314159265358979323846i128 as int }
spec fn scale_factor() -> int { 100000000000000000000i128 as int }

fn degrees_to_radians(degrees: i64) -> (radians: i64)
    ensures radians as int == (degrees as int * pi_approx()) / scale_factor() / 180
// </vc-spec>
// <vc-code>
{
    proof { lemma_scaling(); }
    let scaled_pi_int = compute_scaled_pi_int();
    let scaled_pi: i64 = to_i64(scaled_pi_int);
    (degrees * scaled_pi) / 180
}
// </vc-code>

fn main() {
}

}