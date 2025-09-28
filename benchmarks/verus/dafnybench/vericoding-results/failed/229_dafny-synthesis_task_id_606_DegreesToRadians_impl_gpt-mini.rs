use vstd::prelude::*;

verus! {

// <vc-helpers>
// No helper changes needed.
// </vc-helpers>

// <vc-spec>
spec fn pi_approx() -> int { 314159265358979323846i128 as int }
spec fn scale_factor() -> int { 100000000000000000000i128 as int }

fn degrees_to_radians(degrees: i64) -> (radians: i64)
    ensures radians as int == (degrees as int * pi_approx()) / scale_factor() / 180
// </vc-spec>
// <vc-code>
{
    let radians: i64 = proof {
        let a: int = degrees as int;
        let r_int: int = (a * pi_approx()) / scale_factor() / 180;

        // Basic facts about constants
        assert(pi_approx() >= 0);
        assert(scale_factor() > 0);
        assert(pi_approx() <= scale_factor() * 180);

        if a >= 0 {
            // For a >= 0: num = a * pi_approx() <= a * scale_factor() * 180
            let num = a * pi_approx();
            let denom_scale = scale_factor();
            let denom_180 = 180;
            assert(num <= a * denom_scale * denom_180);

            // Divide by positive denom: preserves <=
            assert(num / denom_scale <= (a * denom_scale * denom_180) / denom_scale);
            // Simplify right-hand side (scale_factor divides the product)
            assert((a * denom_scale * denom_180) / denom_scale == a * denom_180);
            assert(num / denom_scale <= a * denom_180);

            // Divide by 180
            assert((num / denom_scale) / denom_180 <= (a * denom_180) / denom_180);
            assert((a * denom_180) / denom_180 == a);
            assert(r_int <= a);

            // r_int >= 0 because a >= 0 and pi_approx() >= 0
            assert(r_int >= 0);

            // Bounds w.r.t i64
            assert(a <= (i64::MAX as int));
            assert(r_int <= (i64::MAX as int));
            assert(r_int >= (i64::MIN as int));
        } else {
            // a < 0
            let num = a * pi_approx();
            let denom_scale = scale_factor();
            let denom_180 = 180;

            // num = a * pi_approx() >= a * scale_factor() * 180 because multiplying by negative flips inequality
            assert(num >= a * denom_scale * denom_180);

            assert(num / denom_scale >= (a * denom_scale * denom_180) / denom_scale);
            assert((a * denom_scale * denom_180) / denom_scale == a * denom_180);
            assert(num / denom_scale >= a * denom_180);

            assert((num / denom_scale) / denom_180 >= (a * denom_180) / denom_180);
            assert((a * denom_180) / denom_180 == a);
            assert(r_int >= a);

            // r_int <= 0 because a < 0 and pi_approx() >= 0
            assert(r_int <= 0);

            // Bounds w.r.t i64
            assert(a >= (i64::MIN as int));
            assert(r_int >= (i64::MIN as int));
            assert(r_int <= (i64::MAX as int));
        }

        // Return runtime value after proving it fits in i64
        r_int as i64
    };

    proof {
        // Relate runtime result to spec-level integer result
        let a: int = degrees as int;
        let r_int: int = (a * pi_approx()) / scale_factor() / 180;
        assert((radians as int) == r_int);
    }

    radians
}
// </vc-code>

fn main() {
}

}