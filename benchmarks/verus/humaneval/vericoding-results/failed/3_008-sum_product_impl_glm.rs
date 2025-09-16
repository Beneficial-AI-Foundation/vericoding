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
/* helper modified by LLM (iteration 4): Use u128 for sum accumulation to avoid overflow */
fn compute_sum(numbers: &Vec<u32>) -> u64 {
    let mut sum_result: u128 = 0;
    for i in 0..numbers.len() {
        let num = numbers[i] as u128;
        sum_result += num;
    }
    // Assert that the sum is within u64::MAX
    assert(sum_result <= u64::MAX as u128);
    sum_result as u64
}

/* helper modified by LLM (iteration 4): Handle overflow in u64 and then check against u32::MAX */
fn compute_product(numbers: &Vec<u32>) -> Option<u32> {
    let mut product_result: u64 = 1;
    for i in 0..numbers.len() {
        let num = numbers[i] as u64;
        if num == 0 {
            return Some(0);
        }
        if product_result > u64::MAX / num {
            return None;
        }
        product_result *= num;
    }
    if product_result <= u32::MAX as u64 {
        Some(product_result as u32)
    } else {
        None
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
{
    /* code modified by LLM (iteration 4): Updated helpers with overflow handling */
    let sum_result = compute_sum(&numbers);
    let product_result = compute_product(&numbers);
    
    // Verify that our computed sum matches the spec
    proof {
        assert(sum_result as int == sum(numbers@));
    }
    
    // Verify that our computed product matches the spec when it exists
    proof {
        if product_result.is_some() {
            let v = product_result.unwrap();
            assert(v as int == product(numbers@));
        }
    }
    
    (sum_result, product_result)
}
// </vc-code>

}
fn main() {}