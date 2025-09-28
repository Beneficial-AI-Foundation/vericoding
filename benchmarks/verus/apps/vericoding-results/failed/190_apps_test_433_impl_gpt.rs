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
spec fn clamp_mod(x: int, n: int) -> int {
    ((x % n + n) % n)
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
    let n32: i32 = n as i32;
    let a32: i32 = a as i32;
    let b32: i32 = b as i32;

    let tmp: i32 = (((a32 - 1) + b32) % n32 + n32) % n32 + 1;
    let result: i8 = tmp as i8;
    result
}
// </vc-code>


}

fn main() {}