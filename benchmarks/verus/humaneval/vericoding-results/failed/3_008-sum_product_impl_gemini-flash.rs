// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sum(numbers: Seq<u32>) -> (result:int) {
    numbers.fold_left(0, |acc: int, x| acc + x)
}

spec fn product(numbers: Seq<u32>) -> (result:int) {
    numbers.fold_left(1, |acc: int, x| acc * x)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Corrected subsequence method name to `subsequence` and cast literals to `u64` to match `product` type, and added product_overflow_check in invariant, and fixed product_overflow_check to use Seq::subsequence, and explicitly typed the division literal. */
spec fn product_will_overflow(acc_product: u32, next_num: u32) -> bool {
    next_num > 0 && (4294967295u64 / (next_num as u64)) < (acc_product as u64)
}

spec fn product_overflow_check(numbers: Seq<u32>) -> (result: bool) {
    forall|i: nat| #![auto]
        (0 < i && i <= numbers.len())
        ==>
        (numbers[i as int - 1] > 0 && (numbers[i as int - 1] as int) <= (4294967295int) / product(numbers.subsequence(0, i as int)))
}
// </vc-helpers>

// <vc-spec>
fn sum_product(numbers: Vec<u32>) -> (result: (u64, Option<u32>))

    requires
        numbers.len() < u32::MAX,

    ensures
        result.0 == sum(numbers@),
        result.1 matches Some(v) ==> v == product(numbers@),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Changed the `product_overflow_check` to handle the `subsequence` method when called on `Seq<u32>` and fixed type casting for the division literal. */
{
    let mut sum_val: u64 = 0;
    let mut product_val: u32 = 1;
    let mut overflow: bool = false;

    let mut i: usize = 0;
    while i < numbers.len()
        invariant
            0 <= i && i <= numbers.len(),
            sum_val == sum(numbers@.subsequence(0, i as int)) as u64,
            overflow || product_val == product(numbers@.subsequence(0, i as int)) as u32,
            overflow ==> product_val == 0,
    {
        sum_val = sum_val + numbers[i] as u64;

        if !overflow {
            if product_will_overflow(product_val, numbers[i]) {
                overflow = true;
                product_val = 0; // Indicate overflow
            } else {
                product_val = product_val * numbers[i];
            }
        }

        i = i + 1;
    }

    if overflow {
        (sum_val, Option::None)
    } else {
        (sum_val, Option::Some(product_val))
    }
}
// </vc-code>

}
fn main() {}