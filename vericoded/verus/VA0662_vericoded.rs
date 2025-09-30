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
spec fn next(start: int, add: bool, k: int) -> int {
    if add { start + k } else { start * 2 }
}

proof fn lemma_next_preserves_ge1(start: int, k: int, add: bool)
    requires
        start >= 1,
        k >= 1,
    ensures
        next(start, add, k) >= 1,
{
    if add {
        assert(start + k >= 2);
    } else {
        assert(start * 2 >= 2);
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
    n
}
// </vc-code>


}

fn main() {}