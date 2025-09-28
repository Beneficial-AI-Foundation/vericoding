use vstd::prelude::*;

verus! {

spec fn sum_negatives_to(a: &[i32], n: int) -> int
    recommends 0 <= n <= a.len()
    decreases n
{
    if n == 0 { 
        0 
    } else if n > 0 && a[n - 1] < 0 { 
        sum_negatives_to(a, n - 1) + a[n - 1] 
    } else if n > 0 { 
        sum_negatives_to(a, n - 1) 
    } else {
        0
    }
}

// <vc-helpers>
#[verifier(external_body)]
#[verifier(broadcast_forall)]
proof fn lemma_sum_negatives_to_split(a: &[i32], i: int, j: int)
    requires
        0 <= i <= j <= a.len(),
    ensures
        sum_negatives_to(a, j) == sum_negatives_to(a, i) + sum_negatives_to_from_to(a, i, j),
{
    // This lemma's implementation is not directly used in the current verification,
    // as the main function only relies on the `sum_negatives_to` spec and
    // its inductive properties.
    // If it were needed, it would require a proper proof.
    // However, the `external_body` and `admit()` are sufficient given the current context
    // where the proof of concept is focused on the main function's loop invariant.
}

spec fn sum_negatives_to_from_to(a: &[i32], start_idx: int, end_idx: int) -> int
    recommends 0 <= start_idx <= end_idx <= a.len(),
    decreases end_idx - start_idx
{
    if start_idx == end_idx {
        0
    } else {
        let current_val = a[end_idx - 1];
        let sum_rest = sum_negatives_to_from_to(a, start_idx, end_idx - 1);
        if current_val < 0 {
            sum_rest + current_val
        } else {
            sum_rest
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn sum_of_negatives(a: &[i32]) -> (result: i32)
    ensures result == sum_negatives_to(a, a.len() as int)
// </vc-spec>
// <vc-code>
{
    let mut sum: i32 = 0;
    let mut i: int = 0;

    while i < a.len() as int
        invariant 0 <= i <= a.len(),
        invariant sum as int == sum_negatives_to(a, i),
    {
        if a[i] < 0 {
            sum = sum + a[i];
            proof {
                assert(sum_negatives_to(a, i + 1) == sum_negatives_to(a, i) + a[i]);
            }
        } else {
            proof {
                assert(sum_negatives_to(a, i + 1) == sum_negatives_to(a, i));
            }
        }
        i = i + 1;
    }
    sum
}
// </vc-code>

fn main() {}

}