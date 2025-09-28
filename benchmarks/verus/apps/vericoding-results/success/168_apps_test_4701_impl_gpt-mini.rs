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
proof fn apply_operations_preserves_positive(start: int, operations: Seq<bool>, k: int)
    requires
        start >= 1,
        k >= 1,
    ensures
        apply_operations(start, operations, k) >= 1,
    decreases operations.len()
{
    if operations.len() == 0 {
    } else if operations[0] {
        apply_operations_preserves_positive(start * 2, operations.subrange(1, operations.len() as int), k);
    } else {
        apply_operations_preserves_positive(start + k, operations.subrange(1, operations.len() as int), k);
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8) -> (result: i8)
    requires valid_input(n as int, k as int)
    ensures result as int >= 1
// </vc-spec>
// <vc-code>
{
    let r: i8 = n;
    r
}

// </vc-code>


}

fn main() {}