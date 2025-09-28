// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, k: int) -> bool {
    n >= 1 && k >= 1
}

spec fn apply_operations(start: int, operations: Seq<bool>, k: int) -> int
    decreases operations.len()
{
    if operations.len() == 0 {
        start
    } else if operations[0] {
        apply_operations(start * 2, operations.subrange(1, operations.len() as int), k)
    } else {
        apply_operations(start + k, operations.subrange(1, operations.len() as int), k)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): added spec to prove result is >= 1 */
fn min(a: i8, b: i8) -> (result: i8)
    requires
        a >= 1,
        b >= 1,
    ensures
        result >= 1,
        result == if a < b { a } else { b },
{
    if a < b { a } else { b }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8) -> (result: i8)
    requires valid_input(n as int, k as int)
    ensures result as int >= 1
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): logic is now provably correct with the updated min helper spec */
    let op1_opt = n.checked_mul(2);
    let op2_opt = n.checked_add(k);
    match (op1_opt, op2_opt) {
        (Some(op1), Some(op2)) => min(op1, op2),
        (Some(op1), None) => op1,
        (None, Some(op2)) => op2,
        (None, None) => n,
    }
}
// </vc-code>


}

fn main() {}