// <vc-preamble>
use vstd::prelude::*;

verus! {
    spec fn valid_input(n: int, a: int, b: int) -> bool {
        n >= 1 && 1 <= a <= n && -100 <= b <= 100
    }
    
    spec fn final_entrance(n: int, a: int, b: int) -> int {
        ((a - 1 + b) % n + n) % n + 1
    }
    
    spec fn valid_output(result: int, n: int) -> bool {
        1 <= result <= n
    }
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: i8, b: i8) -> (result: i8)
    requires 
        valid_input(n as int, a as int, b as int)
    ensures 
        valid_output(result as int, n as int),
        result as int == final_entrance(n as int, a as int, b as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fix proof block to correctly relate computed r to specification function */
    let n_i16 = n as i16;
    let a_i16 = a as i16;
    let b_i16 = b as i16;
    let total = (a_i16 - 1) + b_i16;
    let mut r = total % n_i16;
    if r < 0 {
        r += n_i16;
    }
    let result = (r + 1) as i8;
    proof {
        let n_int = n as int;
        let a_int = a as int;
        let b_int = b as int;
        let total_int = (a_int - 1) + b_int;
        let spec_result = final_entrance(n_int, a_int, b_int);
        // Unfold specification function
        assert(spec_result == ((total_int % n_int) + n_int) % n_int + 1);
        // Our computed r equals the non-negative modulo
        assert(r as int == ((total_int % n_int) + n_int) % n_int);
        // Therefore spec_result equals r + 1
        assert(spec_result == (r as int) + 1);
        // Our result is r + 1
        assert(result as int == (r as int) + 1);
        assert(result as int == spec_result);
    }
    result
}
// </vc-code>


}

fn main() {}