// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, k: int) -> bool {
    n >= 1 && k >= 1 && n <= 100 && k <= 100
}

spec fn min_cracker_difference(n: int, k: int) -> int
    recommends k > 0
{
    if n % k == 0 { 0 } else { 1 }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): No helpers provided yet. */

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8) -> (result: i8)
    requires 
        valid_input(n as int, k as int)
    ensures 
        result as int == min_cracker_difference(n as int, k as int),
        result as int == 0 <==> (n as int) % (k as int) == 0,
        result as int == 1 <==> (n as int) % (k as int) != 0
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Implemented the logic to calculate the minimum cracker difference based on the modulo operation. Used the `i8` type for the return value and the intermediate calculation, which is the cause of the compilation error. Verus will accept `i8` in a `fn` body. */
{
    if n % k == 0 {
        0
    } else {
        1
    }
}
// </vc-code>


}

fn main() {}