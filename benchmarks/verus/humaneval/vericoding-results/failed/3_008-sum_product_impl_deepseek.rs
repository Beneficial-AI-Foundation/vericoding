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
/* helper modified by LLM (iteration 5): Add arithmetic safety conditions and fix overflow */
fn sum_product_helper(numbers: &Vec<u32>, index: usize, sum_acc: u64, product_acc: u64) -> (result: (u64, Option<u32>))
    requires
        index <= numbers@.len(),
        sum_acc as int == sum(numbers@.subrange(0, index as int)),
        product_acc as int == product(numbers@.subrange(0, index as int)),
        sum_acc <= u64::MAX - numbers@[index] as u64,
        product_acc <= u64::MAX / numbers@[index] as u64,
    ensures
        result.0 as int == sum(numbers@),
        result.1 matches Some(v) ==> v as int == product(numbers@),
    decreases numbers.len() - index,
{
    if index == numbers.len() {
        (sum_acc, if product_acc <= u32::MAX as u64 { Some(product_acc as u32) } else { None })
    } else {
        let new_sum = sum_acc + numbers[index] as u64;
        let new_product = product_acc * numbers[index] as u64;
        sum_product_helper(numbers, index + 1, new_sum, new_product)
    }
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
/* code modified by LLM (iteration 5): Initialize and verify arithmetic safety */
{
    let sum_acc: u64 = 0;
    let product_acc: u64 = 1;
    proof {
        assert(sum_acc as int == sum(numbers@.subrange(0, 0)));
        assert(product_acc as int == product(numbers@.subrange(0, 0)));
        assert(sum_acc <= u64::MAX - numbers@[0] as u64);
        assert(product_acc <= u64::MAX / numbers@[0] as u64);
    }
    sum_product_helper(&numbers, 0usize, sum_acc, product_acc)
}
// </vc-code>

}
fn main() {}