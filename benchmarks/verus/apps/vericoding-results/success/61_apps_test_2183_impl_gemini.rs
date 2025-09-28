// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_brother_numbers(a: int, b: int) -> bool {
    1 <= a <= 3 && 1 <= b <= 3 && a != b
}

spec fn late_brother(a: int, b: int) -> int
    recommends valid_brother_numbers(a, b)
{
    6 - a - b
}

spec fn is_valid_result(a: int, b: int, result: int) -> bool {
    valid_brother_numbers(a, b) ==> 
        (1 <= result <= 3 && result != a && result != b)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Added comments explaining the automated proof. */
proof fn lemma_late_brother_is_valid(a: int, b: int)
    requires
        valid_brother_numbers(a, b),
    ensures
        is_valid_result(a, b, late_brother(a, b)),
{
    // The properties of late_brother(a, b) are provable by the SMT solver
    // given the small integer range for a and b from valid_brother_numbers.
    // The solver can deduce that:
    // 1. a + b is in the range [3, 5], which implies 1 <= 6 - (a + b) <= 3.
    // 2. 2*a + b != 6 and a + 2*b != 6, which implies result != a and result != b.
}
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8) -> (result: i8)
    requires 
        valid_brother_numbers(a as int, b as int)
    ensures 
        is_valid_result(a as int, b as int, result as int) &&
        result as int == late_brother(a as int, b as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Wrapped lemma call in proof block to fix ghost context error. */
    let result = 6 - a - b;
    proof {
        lemma_late_brother_is_valid(a as int, b as int);
    }
    result
}
// </vc-code>


}

fn main() {}