use vstd::prelude::*;

verus! {

// <vc-helpers>
// no helpers needed
// </vc-helpers>

// <vc-spec>
spec fn pi_approx() -> int { 314159265358979323846i128 as int }
spec fn scale_factor() -> int { 100000000000000000000i128 as int }

fn degrees_to_radians(degrees: i64) -> (radians: i64)
    ensures radians as int == (degrees as int * pi_approx()) / scale_factor() / 180
// </vc-spec>
// <vc-code>
{
    let ghost d_int: int = degrees as int;
    let ghost r_spec: int = (d_int * pi_approx()) / scale_factor() / 180;

    proof {
        assert(0 < scale_factor());
        assert(0 < 180);
        assert(0 < pi_approx());
        assert(pi_approx() < 180 * scale_factor());

        if d_int >= 0 {
            assert(0 <= d_int * pi_approx());
            assert(d_int * pi_approx() <= d_int * (180 * scale_factor()));

            let q1: int = (d_int * pi_approx()) / scale_factor();
            assert(0 <= q1);
            assert(q1 <= (d_int * (180 * scale_factor())) / scale_factor());
            assert((d_int * (180 * scale_factor())) / scale_factor() == d_int * 180);

            assert(0 <= r_spec);
            assert(r_spec <= (d_int * 180) / 180);
            assert((d_int * 180) / 180 == d_int);

            assert(i64::MIN as int <= 0);
            assert(0 <= r_spec);
            assert(i64::MIN as int <= r_spec);

            assert(d_int <= i64::MAX as int);
            assert(r_spec <= d_int);
            assert(r_spec <= i64::MAX as int);
        } else {
            assert(d_int * pi_approx() <= 0);
            assert(d_int * pi_approx() >= d_int * (180 * scale_factor()));

            let q1: int = (d_int * pi_approx()) / scale_factor();
            assert(q1 <= 0);
            assert(q1 >= (d_int * (180 * scale_factor())) / scale_factor());
            assert((d_int * (180 * scale_factor())) / scale_factor() == d_int * 180);

            assert(r_spec <= 0);
            assert(r_spec >= (d_int * 180) / 180);
            assert((d_int * 180) / 180 == d_int);

            assert(i64::MIN as int <= d_int);
            assert(d_int <= r_spec);
            assert(i64::MIN as int <= r_spec);

            assert(0 <= i64::MAX as int);
            assert(r_spec <= 0);
            assert(r_spec <= i64::MAX as int);
        }
    }

    let r: i64 = r_spec as i64;
    assert(r as int == r_spec);
    r
}
// </vc-code>

fn main() {
}

}