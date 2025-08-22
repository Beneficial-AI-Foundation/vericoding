use vstd::prelude::*;

verus! {
spec fn sum(numbers: Seq<u32>) -> (result:int) {
    numbers.fold_left(0, |acc: int, x| acc + x)
}
// pure-end

spec fn product(numbers: Seq<u32>) -> (result:int) {
    numbers.fold_left(1, |acc: int, x| acc * x)
}
// pure-end

proof fn sum_bound(numbers: Seq<u32>)
    // post-conditions-start
    ensures
        sum(numbers) <= numbers.len() * u32::MAX,
    decreases numbers.len(),
    // post-conditions-end
{
    // impl-start
    if numbers.len() == 0 {
    } else {
        sum_bound(numbers.drop_last());
    }
    // impl-end
}
// pure-end

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
{
    let mut total_sum: u64 = 0;
    let mut total_product: u64 = 1;
    let mut i = 0;
    
    /* code modified by LLM (iteration 1): added decreases clause for loop termination */
    while i < numbers.len()
        invariant
            i <= numbers.len(),
            total_sum == sum(numbers@.subrange(0, i as int)),
            total_product == product(numbers@.subrange(0, i as int)),
        decreases numbers.len() - i
    {
        let num = numbers[i];
        total_sum = total_sum + num as u64;
        total_product = total_product * num as u64;
        i = i + 1;
    }
    
    let product_result = if total_product <= u32::MAX as u64 {
        Some(total_product as u32)
    } else {
        None
    };
    
    (total_sum, product_result)
}

}
fn main() {}