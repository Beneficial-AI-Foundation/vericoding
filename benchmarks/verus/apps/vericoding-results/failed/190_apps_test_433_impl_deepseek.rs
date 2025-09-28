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
fn mod_positive(x: i16, m: i16) -> (r: i16)
    requires
        m > 0,
    ensures
        0 <= r < m,
        r as int == x as int % m as int
{
    /* helper modified by LLM (iteration 5): Fixed modulo computation with proper casting and verification */
    let raw_r = x % m;
    if raw_r < 0 {
        raw_r + m
    } else {
        raw_r
    }
}
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
    /* code modified by LLM (iteration 5): Fixed modulo computation and proof steps */
    proof {
        let n_int = n as int;
        let a_int = a as int;
        let b_int = b as int;
        assert(valid_input(n_int, a_int, b_int));
    }
    
    let n16 = n as i16;
    let a16 = a as i16;
    let b16 = b as i16;
    let offset = a16 - 1 + b16;
    let mod_result = mod_positive(offset, n16);
    let result_int = mod_result + 1;
    (result_int as i8)
}
// </vc-code>


}

fn main() {}