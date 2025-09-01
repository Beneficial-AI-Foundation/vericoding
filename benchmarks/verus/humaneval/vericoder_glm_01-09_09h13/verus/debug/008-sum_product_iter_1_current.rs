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
    let mut sum_acc: u64 = 0;
    let mut product_acc: Option<u32> = Some(1);

    for i in 0..numbers.len()
        invariant
            0 <= i <= numbers.len(),
            sum_acc == sum(numbers@.subrange(0, i)) as u64,
            product_acc == 
                if product(numbers@.subrange(0, i)) <= (u32::MAX as int) {
                    Some(product(numbers@.subrange(0, i)) as u32)
                } else {
                    None
                }
    {
        let num = numbers[i];
        sum_acc = sum_acc + (num as u64);

        product_acc = match product_acc {
            Some(p) => {
                let p_u64 = p as u64;
                let num_u64 = num as u64;
                let new_product_u64 = p_u64 * num_u64;
                if new_product_u64 <= (u32::MAX as u64) {
                    Some(new_product_u64 as u32)
                } else {
                    None
                }
            },
            None => {
                if num == 0 {
                    Some(0)
                } else {
                    None
                }
            }
        };
    }

    (sum_acc, product_acc)
}
// </vc-code>

fn main() {}
}