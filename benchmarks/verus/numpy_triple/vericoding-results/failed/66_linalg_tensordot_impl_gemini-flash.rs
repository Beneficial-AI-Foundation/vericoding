// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): This removes the `requires` clause from the `seq_sum_range` spec function as spec functions cannot have `requires`/`ensures` clauses in Verus. This caused a compilation error. */
spec fn seq_sum_range(a: Seq<i32>, b: Seq<i32>, start: nat, end: nat) -> int
{
    if start == end {
        0
    } else {
        a[start as int] * b[start as int] + seq_sum_range(a, b, (start + 1) as nat, end)
    }
}
// </vc-helpers>

// <vc-spec>
spec fn dot_product_recursive(a: Seq<i32>, b: Seq<i32>, i: nat) -> int
    decreases a.len() - i
{
    if i >= a.len() {
        0
    } else {
        a[i as int] * b[i as int] + dot_product_recursive(a, b, i + 1)
    }
}

spec fn dot_product(a: Seq<i32>, b: Seq<i32>) -> int {
    dot_product_recursive(a, b, 0)
}

fn tensordot(a: Vec<i32>, b: Vec<i32>, axes: usize) -> (result: i32)
    requires 
        a.len() == b.len(),
        axes == 1,
    ensures result == dot_product(a@, b@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): This code now uses a direct iterative approach with a loop. The loop invariant and assertions are carefully designed to prove that the computed sum equals the `dot_product` of the input sequences. The previous version contained `assume` statements, which caused a verification bypass, and also had an incorrect loop invariant. */
{
    let mut sum: i32 = 0;
    if a.len() > 0 {
        assert(a.len() as nat == b.len() as nat);

        let mut i: usize = 0;
        while i < a.len()
            invariant
                0 <= i && i <= a.len(),
                sum as int == seq_sum_range(a@, b@, 0, i as nat),
                a.len() == b.len(),
        {
            sum = sum + (a[i] * b[i]);
            proof {
                assert(seq_sum_range(a@, b@, 0, (i + 1) as nat) == seq_sum_range(a@, b@, 0, i as nat) + a@[i as int] * b@[i as int]);
            }
            i = i + 1;
        }

        proof {
            assert(sum as int == seq_sum_range(a@, b@, 0, a.len() as nat));
            assert(seq_sum_range(a@, b@, 0, a.len() as nat) == dot_product(a@, b@));
        }
    }
    sum
}
// </vc-code>

}
fn main() {}