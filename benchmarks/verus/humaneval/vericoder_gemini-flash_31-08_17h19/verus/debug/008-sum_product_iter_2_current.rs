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
fn checked_product_u32(a: u32, b: u32) -> (res: (u32, bool))
    ensures
        res.1 == true <==> (a as u64) * (b as u64) <= u32::MAX as u64,
        res.1 == true ==> (res.0 == a * b),
{
    let val: u64 = (a as u64) * (b as u64);
    if val <= u32::MAX as u64 {
        (val as u32, true)
    } else {
        (0, false)
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
    // impl-start
    let mut current_sum: u64 = 0;
    let mut current_product: Option<u32> = Some(1);

    let mut i: usize = 0;
    while i < numbers.len()
        invariant
            numbers.len() < u32::MAX,
            0 <= i,
            i <= numbers.len(),
            current_sum == sum(numbers@.subsequence(0, i)) as u64,
            ({
                if current_product.is_some() {
                    current_product.unwrap() == product(numbers@.subsequence(0, i)) as u32
                } else {
                    product(numbers@.subsequence(0, i)) as u64 > u32::MAX
                }
            }),
            current_product.is_some() ==> (current_product.unwrap() as u64) < u64::MAX, // Added this invariant to avoid overflow issues in checked_product_u32
    {
        current_sum = current_sum + (numbers[i] as u64);
        proof {
            assert(current_sum == sum(numbers@.subsequence(0, i + 1)) as u64);
        }

        if let Some(prod_val) = current_product {
            let (new_prod, ok) = checked_product_u32(prod_val, numbers[i]);
            if ok {
                current_product = Some(new_prod);
            } else {
                current_product = None;
            }
        }
        proof {
            assert({
                if current_product.is_some() {
                    current_product.unwrap() == product(numbers@.subsequence(0, i + 1)) as u32
                } else {
                    product(numbers@.subsequence(0, i + 1)) as u64 > u32::MAX
                }
            });
        }
        i = i + 1;
    }
    (current_sum, current_product)
    // impl-end
}
// </vc-code>

fn main() {}
}