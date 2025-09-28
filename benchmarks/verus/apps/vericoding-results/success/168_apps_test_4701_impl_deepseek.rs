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

// Applies the operations to the current value
spec fn simple_apply(current: int, op: bool, k: int) -> int {
    if op {
        current * 2
    } else {
        current + k
    }
}

// Helper lemma that shows that applying operations preserves positivity
proof fn operations_preserve_positivity(current: int, operations: Seq<bool>, k: int)
    requires
        current >= 1,
        k >= 1,
    ensures
        apply_operations(current, operations, k) >= 1,
    decreases operations.len()
{
    if operations.len() == 0 {
        // Base case: no operations, result is current >= 1
    } else {
        // Recursive case: show first operation preserves positivity
        let next = simple_apply(current, operations[0], k);
        assert(next >= 1) by {
            if operations[0] {
                assert(current * 2 >= 1);
            } else {
                assert(current + k >= 1);
            }
        };
        // Apply induction hypothesis
        operations_preserve_positivity(next, operations.subrange(1, operations.len() as int), k);
    }
}
/* helper modified by LLM (iteration 2): maintained original lemma */
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8) -> (result: i8)
    requires valid_input(n as int, k as int)
    ensures result as int >= 1
// </vc-spec>
// <vc-code>
{
    // Convert inputs to nat for specification reasoning
    proof {
        let n_int = n as int;
        let k_int = k as int;
        // Empty sequence of operations gives result = n >= 1
        operations_preserve_positivity(n_int, Seq::empty(), k_int);
    }
    
    /* code modified by LLM (iteration 2): moved int conversions to proof block */
    // Trivial implementation: just return n as the answer
    let result = n;
    
    // The result is valid since n >= 1
    result
}
// </vc-code>


}

fn main() {}