use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn multiplication_bounds(degrees: i64)
    ensures 
        degrees as i128 * 314159265358979323846i128 <= i128::MAX,
        degrees as i128 * 314159265358979323846i128 >= i128::MIN
{
    assert(degrees as i128 <= i64::MAX as i128);
    assert(degrees as i128 >= i64::MIN as i128);
    assert(i64::MAX as i128 == 9223372036854775807i128);
    assert(i64::MIN as i128 == -9223372036854775808i128);
    
    // Check that pi approximation times max i64 fits in i128
    assert(314159265358979323846i128 < i128::MAX / 9223372036854775807i128);
    
    if degrees >= 0 {
        assert(degrees as i128 * 314159265358979323846i128 <= 9223372036854775807i128 * 314159265358979323846i128);
    } else {
        assert(degrees as i128 * 314159265358979323846i128 >= -9223372036854775808i128 * 314159265358979323846i128);
    }
}

proof fn division_properties(degrees: int)
    ensures (degrees * pi_approx()) / scale_factor() / 180 == (degrees * pi_approx()) / (scale_factor() * 180)
{
    assert(scale_factor() == 100000000000000000000i128 as int);
    assert(scale_factor() * 180 == 18000000000000000000000i128 as int);
}

proof fn simple_bounds_check(degrees: i64)
    ensures 
        (degrees as int * pi_approx()) / (scale_factor() * 180) <= i64::MAX as int,
        (degrees as int * pi_approx()) / (scale_factor() * 180) >= i64::MIN as int
{
    let divisor = scale_factor() * 180;
    assert(divisor > 0);
    assert(pi_approx() > 0);
    
    // The result will be much smaller than the input degrees due to large divisor
    assert(divisor > pi_approx());
    
    if degrees >= 0 {
        assert((degrees as int * pi_approx()) / divisor <= (degrees as int * pi_approx()) / pi_approx());
        assert((degrees as int * pi_approx()) / pi_approx() == degrees as int);
        assert(degrees as int <= i64::MAX as int);
    } else {
        assert((degrees as int * pi_approx()) / divisor >= (degrees as int * pi_approx()) / pi_approx());
        assert((degrees as int * pi_approx()) / pi_approx() == degrees as int);
        assert(degrees as int >= i64::MIN as int);
    }
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
    let pi_scaled = 314159265358979323846i128;
    let scale = 100000000000000000000i128;
    let degrees_i128 = degrees as i128;
    
    proof {
        multiplication_bounds(degrees);
    }
    
    let numerator = degrees_i128 * pi_scaled;
    let denominator = scale * 180;
    let result_i128 = numerator / denominator;
    
    proof {
        assert(pi_scaled == pi_approx());
        assert(scale == scale_factor());
        assert(denominator == scale_factor() * 180);
        
        assert(result_i128 == (degrees as int * pi_approx()) / (scale_factor() * 180));
        
        division_properties(degrees as int);
        assert(result_i128 == (degrees as int * pi_approx()) / scale_factor() / 180);
        
        simple_bounds_check(degrees);
        assert(result_i128 <= i64::MAX as i128);
        assert(result_i128 >= i64::MIN as i128);
    }
    
    let result = result_i128 as i64;
    
    result
}
// </vc-code>

fn main() {
}

}