// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_prime_number(num: int) -> bool {
    num >= 2 && forall|k: int| 2 <= k < num ==> #[trigger] (num % k) != 0
}

// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no change, previous code already correct */
proof fn lemma_divides_implies_not_prime(num: int, k: int)
    requires
        num >= 2,
        2 <= k < num,
        num % k == 0,
    ensures
        !is_prime_number(num)
{
    assert(exists|j: int| 2 <= j < num && (num % j) == 0) by { /* This is the correct way to specify the witness for exists. */
        // The witness for the exists statement is `k`
    };
}
// </vc-helpers>

// <vc-spec>
fn count_up_to(n: i8) -> (result: Vec<i8>)
    requires n as int >= 0
    ensures 
        forall|i: int| 0 <= i < result.len() ==> is_prime_number(#[trigger] result[i] as int),
        forall|i: int| 0 <= i < result.len() ==> #[trigger] (result[i] as int) < (n as int),
        forall|p: int| 2 <= p < (n as int) && is_prime_number(p) ==> result@.contains(p as i8),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> #[trigger] (result[i] as int) < #[trigger] (result[j] as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Changed ghost variable `n_int` to regular `n` in loop condition and casting to int only when used in spec functions */
{
    let mut result: Vec<i8> = Vec::new();
    let mut current_num: i8 = 2;

    while (current_num as int) < (n as int)
        invariant
            result.spec_v().len() == result.len(),
            (current_num as int) <= (n as int) + 1,
            (current_num as int) >= 2,
            // All elements in result are prime numbers
            forall|i: int| 0 <= i < result.len() ==> is_prime_number(#[trigger] result[i] as int),
            // All elements in result are less than n
            forall|i: int| 0 <= i < result.len() ==> #[trigger] (result[i] as int) < (n as int),
            // All prime numbers found so far (less than current_num) are in result
            forall|p: int|
                2 <= p < (current_num as int) && is_prime_number(p)
                ==>
                result.spec_v().contains(p as i8)
            ,
            // result is sorted
            forall|i: int, j: int| 0 <= i < j < result.len() ==> #[trigger] (result[i] as int) < #[trigger] (result[j] as int),
            // No duplicates in result
            forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],
        decreases (n as int) - (current_num as int)
    {
        if is_prime_number(current_num as int) {
            result.push(current_num);
        }
        current_num = current_num + 1;
    }
    result
}
// </vc-code>


}

fn main() {}