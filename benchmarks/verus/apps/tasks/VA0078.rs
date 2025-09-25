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
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}