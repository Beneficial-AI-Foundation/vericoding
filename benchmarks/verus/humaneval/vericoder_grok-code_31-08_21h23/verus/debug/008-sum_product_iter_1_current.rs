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
[Updated or new helper code and proofs needed for verification]
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
    let view = numbers@;
    let mut sum_u64: u64 = 0;
    let mut index: usize = 0;
    tracked let mut sum_acc: int = 0;
    tracked let mut product_acc: int = 1;

    while index < numbers.len()
        invariant
            index <= view.len(),
            sum_acc == sum(view.subrange(0, index as int)),
            product_acc == product(view.subrange(0, index as int)),
            sum_u64 as int == sum_acc,
    {
        let val_u64 = numbers[index] as u64;
        sum_u64 += val_u64;
        let val_int = numbers[index] as int;

        proof! {
            sum_acc = sum_acc + val_int;
            product_acc = product_acc * val_int;
        };

        index += 1;
    }

    assert(sum_u64 as int == sum(view));
    assert(product_acc == product(view));

    let u32_max_int = u32::MAX as int;
    let product_opt = 
        if product_acc <= u32_max_int && 0 <= product_acc {
            Some(product_acc as u32)
        } else {
            None
        };

    (sum_u64, product_opt)
}
// </vc-code>

fn main() {}
}