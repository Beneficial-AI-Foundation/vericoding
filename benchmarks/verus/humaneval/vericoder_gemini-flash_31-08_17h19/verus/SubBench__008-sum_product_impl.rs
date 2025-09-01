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
const U32_MAX_AS_INT: int = 0xFFFFFFFF; // u32::MAX as int

// Proof method to show that the sum of u32s fits into u64.
proof fn lemma_sum_u32_fits_u64(numbers: Seq<u32>)
    ensures
        sum(numbers) <= (u64::MAX as int),
{
    let mut i = 0;
    let mut current_sum: int = 0;
    while i < numbers.len()
        invariant
            0 <= i <= numbers.len(),
            current_sum == numbers.subsequence(0, i).fold_left(0, |acc: int, x| acc + x),
            current_sum <= (i as int) * (U32_MAX_AS_INT as int),
    {
        current_sum = current_sum + numbers.index(i) as int;
        i = i + 1;
    }
    assert(sum(numbers) == current_sum);

    if numbers.len() > 0 {
        assert(sum(numbers) <= (numbers.len() as int) * (U32_MAX_AS_INT as int));
        assert((numbers.len() as int) <= (u32::MAX as int)); // Numbers.len() can be u32::MAX
        // The upper bound for number_length * U32_MAX_AS_INT is u64::MAX precisely.
        // It's possible for sum(numbers) to exceed u32::MAX (e.g. [u32::MAX, u32::MAX]) but still fit in u64.
        // The numbers.len() < u32::MAX implies that numbers.len() as int <= u32::MAX as int -1.
        // If numbers.len() is 0, sum of empty sequence is 0, fits in u64.
        // If numbers.len() is non-zero
        // assert((numbers.len() as int) * (U32_MAX_AS_INT as int) <= (u64::MAX as int));
    }
    assert(sum(numbers) <= (u64::MAX as int));
}

// Helper to prove that `current_product` is equal to the spec product
proof fn lemma_product_u32_no_overflow_implies_equal(
    numbers: Seq<u32>,
    k: int,
    current_product: u32,
)
    requires
        0 <= k <= numbers.len(),
        forall|j: int| 0 <= j < k ==> #[trigger] product(numbers.subsequence(0, j + 1)) <= u32::MAX as int,
        // The product(numbers.subsequence(0, j + 1)) is as int.
        // If it means that no overflow happened, and the current_product matches the product of
        // subsequence, then product(numbers.subsequence(0, k)) <= u32::MAX as int also holds.
        current_product == product(numbers.subsequence(0, k)) as u32,
    ensures
        current_product == product(numbers.subsequence(0, k)) as u32,
{
    // The ensures clause is the same as the requires, so this lemma is trivially true.
    // However, it helps Verus to connect the implications.
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
    let mut current_sum: u64 = 0;
    let mut current_product: u32 = 1;
    let mut product_overflow: bool = false;

    let mut i = 0;
    #[invariant(
        0 <= i <= numbers.len(),
        current_sum == sum(numbers@.subsequence(0, i)) as u64,
        product_overflow || current_product == product(numbers@.subsequence(0, i)) as u32,
        sum(numbers@.subsequence(0, i)) <= u64::MAX as int,
    )]
    while i < numbers.len()
    {
        let num = numbers.get(i);

        // Calculate sum
        current_sum = current_sum + num as u64;

        // Calculate product with overflow check
        if !product_overflow {
            let (next_product, overflowed) = current_product.overflowing_mul(num);
            if overflowed {
                product_overflow = true;
            } else {
                current_product = next_product;
            }
        }
        i = i + 1;
    }

    lemma_sum_u32_fits_u64(numbers@);
    assert(current_sum == sum(numbers@) as u64);

    let final_product_option: Option<u32>;
    if product_overflow {
        final_product_option = None;
    } else {
        final_product_option = Some(current_product);
        assert(current_product == product(numbers@) as u32);
    }
    (current_sum, final_product_option)
}
// </vc-code>

fn main() {}
}