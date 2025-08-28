use vstd::prelude::*;

verus! {

spec fn sum(numbers: Seq<u32>) -> (result:int) {
    numbers.fold_left(0, |acc: int, x| acc + x)
}
// pure-end
// pure-end

spec fn product(numbers: Seq<u32>) -> (result:int) {
    numbers.fold_left(1, |acc: int, x| acc * x)
}
// pure-end

// <vc-helpers>
proof fn sum_bound(numbers: Seq<u32>)
    ensures
        sum(numbers) <= numbers.len() * u32::MAX,
    decreases numbers.len(),
{
    if numbers.len() == 0 {
    } else {
        sum_bound(numbers.drop_last());
    }
}

proof fn product_overflow_lemma(numbers: Seq<u32>, acc: int, i: int)
    requires
        0 <= i <= numbers.len(),
        acc <= u32::MAX,
        forall|j: int| 0 <= j < i ==> numbers[j] <= u32::MAX,
    ensures
        acc * product(numbers.subrange(i, numbers.len() as int)) <= u32::MAX ==> 
            product(numbers) <= u32::MAX,
    decreases numbers.len() - i,
{
    if i == numbers.len() {
    } else {
        product_overflow_lemma(numbers, acc, i + 1);
    }
}
// </vc-helpers>

// <vc-spec>
fn sum_product(numbers: Vec<u32>) -> (result: (u64, Option<u32>))
    // pre-conditions-start
    requires
        numbers.len() < u32::MAX,
    // pre-conditions-end
    // post-conditions-start
    ensures
        result.0 == sum(numbers@),
        result.1 matches Some(v) ==> v == product(numbers@),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut total_sum: u64 = 0;
    let mut total_product: u32 = 1;
    let mut product_valid = true;
    let mut i = 0;

    while i < numbers.len()
        invariant
            0 <= i <= numbers.len(),
            total_sum == sum(numbers@.subrange(0, i as int)),
            product_valid ==> total_product == product(numbers@.subrange(0, i as int)),
            !product_valid ==> exists|j: int| 0 <= j < i && total_product.checked_mul(numbers@[j]).is_none(),
            total_sum <= u64::MAX,
    {
        let num = numbers[i];
        total_sum = total_sum + num as u64;
        
        if product_valid {
            match total_product.checked_mul(num) {
                Some(new_product) => {
                    total_product = new_product;
                },
                None => {
                    product_valid = false;
                }
            }
        }
        i = i + 1;
    }

    let result_product = if product_valid {
        Some(total_product)
    } else {
        None
    };

    (total_sum, result_product)
}
// </vc-code>

}
fn main() {}