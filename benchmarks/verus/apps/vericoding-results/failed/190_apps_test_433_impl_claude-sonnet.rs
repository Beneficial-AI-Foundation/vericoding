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
/* helper modified by LLM (iteration 5): removed requires/ensures from spec function */
spec fn lemma_mod_arithmetic(a: int, b: int, n: int) -> bool
{
    n > 0 ==> ((a + b) % n + n) % n == (a + b) % n + (if (a + b) % n < 0 { n } else { 0 })
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
    /* code modified by LLM (iteration 5): simplified implementation without ghost variables */
    let sum = (a - 1) + b;
    let mod_result = sum % n;
    let adjusted = if mod_result < 0 {
        mod_result + n
    } else {
        mod_result
    };
    let result = adjusted + 1;
    
    result
}
// </vc-code>


}

fn main() {}