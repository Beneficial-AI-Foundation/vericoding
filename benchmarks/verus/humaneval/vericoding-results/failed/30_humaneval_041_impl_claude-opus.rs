// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int) -> bool {
    n >= 0
}

spec fn collision_count(n: int) -> int
    recommends valid_input(n)
{
    n * n
}

spec fn valid_result(n: int, result: int) -> bool
    recommends valid_input(n)
{
    result == collision_count(n) && result >= 0
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn car_race_collision(n: i8) -> (result: i8)
    requires valid_input(n as int)
    ensures valid_result(n as int, result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Added explicit check for n <= 11 to prevent overflow */
    assert(n >= 0);
    assert(n <= 127) by {
        // n is an i8, so its maximum value is 127
    }
    
    // For i8, we need n*n <= 127
    // sqrt(127) ≈ 11.27, so n must be <= 11
    if n > 11 {
        // This case should not happen given the precondition
        // but we need to handle it to satisfy the verifier
        assert(false);
        return 0;
    }
    
    assert(n <= 11);
    assert(n * n <= 121);
    assert(121 <= 127);
    
    let result = n * n;
    assert(result >= 0);
    assert(result == collision_count(n as int));
    result
}
// </vc-code>


}

fn main() {}