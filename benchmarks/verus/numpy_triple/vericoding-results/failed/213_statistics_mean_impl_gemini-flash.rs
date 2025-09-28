// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed unreachable code */
fn sum_vec_elements(v: &Vec<i32>) -> (result: i32)
    ensures result as int == vec_sum(v@)
{
    let mut i: nat = 0;
    let mut current_sum: i32 = 0;

    while i < v.len()
        invariant
            i <= v.len(),
            current_sum as int == vec_sum(v@.subsequence(0, i)),
    {
        current_sum = current_sum + v[i];
        i = i + 1;
    }
    current_sum
}
// </vc-helpers>

// <vc-spec>
spec fn vec_sum(a: Seq<i32>) -> int 
    decreases a.len()
{
    if a.len() == 0 {
        0
    } else {
        a[0] as int + vec_sum(a.skip(1))
    }
}

spec fn all_equal(a: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> a[i] == a[j]
}

fn mean(a: Vec<i32>) -> (result: i32)
    requires a.len() > 0,
    ensures 
        /* Core property: mean * count == sum */
        (result as int) * (a.len() as int) == vec_sum(a@),
        /* For constant vectors, mean equals the constant */
        all_equal(a@) ==> result == a[0]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): moved int conversions to ghost variables */
{
    let sum = sum_vec_elements(&a);
    let count = a.len();

    // Use ghost variables for 'int' types to satisfy Verus's type rules
    let ghost exact_sum: int = sum as int;
    let ghost exact_count: int = count as int;
    
    // In integer division, `exact_sum / exact_count` truncates towards zero.
    // Since the Verus `mean` function returns `i32`, it implicitly expects an integer mean.
    // The `ensures` clause `(result as int) * (a.len() as int) == vec_sum(a@)` implies that `vec_sum(a@)` must be divisible by `a.len()`.
    // If this is not generally true, then `mean` would typically return a float type.
    // For this exact type signature, we assume integer division, and check the postcondition.

    let result_val: i32 = (sum / (count as i32)); // Perform i32 division directly

    // Proof to satisfy the first ensures clause (result * count == sum)
    // This will only verify if `exact_sum` is perfectly divisible by `exact_count`.
    // Otherwise, the `ensures` clause can't hold for integer division.
    // The problem statement implies this should be verifiable with integer arithmetic.
    proof {
        assert((result_val as int) * exact_count <= exact_sum); // This always holds for integer division
        // The primary issue is that the `ensures` clause requires exact equality for integer division.
        // This implies that `vec_sum(a@)` must be perfectly divisible by `a.len()`.
        // If not, the `ensures` clause cannot be satisfied with i32 division.
        // The previous `assume` was a bypass, removing it.
        // To satisfy `(result as int) * (a.len() as int) == vec_sum(a@)`, we need:
        // `(sum / (count as i32)) as int * exact_count == exact_sum`
        // This is only true if `exact_sum` is exactly divisible by `exact_count`.
        // The verifier will automatically check this if the division is exact.
    }
    
    result_val
}
// </vc-code>


}
fn main() {}