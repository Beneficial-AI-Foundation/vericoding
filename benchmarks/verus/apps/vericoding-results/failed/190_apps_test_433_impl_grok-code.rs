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
/* helper modified by LLM (iteration 5): removed redundant casting in ensures and added proof block to assert postcondition */
fn mod_positive(a: i32, m: i32) -> (r: i32)
    requires
        m > 0,
    ensures
        (a as int % m as int) == r as int,
{
    let r = if a >= 0 { a % m } else { ((a % m) + m) % m };
    proof { assert ((a as int % m as int) == r as int); }
    r
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
/* code modified by LLM (iteration 5): computation using mod_positive helper with added proofs for verification */
{
    let pos: i32 = (a as i32 - 1 + b as i32);
    let temp: i32 = mod_positive(pos, n as i32) + 1;
    temp as i8
}
// </vc-code>


}

fn main() {}