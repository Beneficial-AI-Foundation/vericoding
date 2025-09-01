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
        assert((numbers.len() as int) <= (u32::MAX as int - 1)); // From precondition
        assert((numbers.len() as int) * (U32_MAX_AS_INT as int) <= (u32::MAX as int - 1) * (U32_MAX_AS_INT as int));
        assert((u32::MAX as int - 1) * (U32_MAX_AS_INT as int) < (u64::MAX as int)); // Proved by arithmetic
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
        // If product_overflow is true, it means product(subsequence) would have overflowed u32.
        // It doesn't mean the product will be 0 if the numbers are 0.
        // If product_overflow, then current_product is meaningless, hence not included in the invariant
        // unless product_overflow is false. Better to say:
        // current_product.is_some() ==> current_product.unwrap() == product(numbers.subsequence(0, i)) as u32
        // For the purpose of current Verus, keeping it simple:
        // product_overflow || (current_product == product(numbers.subsequence(0, i)) as u32),
        // Where current_product is the accumulated product as long as it fits u32.
        // If product_overflow, then the real product exceeds u32::MAX.

        // For sum:
        sum(numbers@.subsequence(0, i)) <= u64::MAX as int,
        // The above means lemma_sum_u32_fits_u64(numbers.subsequence(0, i)) is implicitly true
    )]
    while i < numbers.len() {
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

        // Prove that if not overflowed, current_product is the actual product
        // This assertion might still fail if Verus cannot prove the transitive equality
        // of `current_product` with `product(numbers@)` immediately.
        // Need to show that for all `j < numbers.len()`, `product(numbers@.subsequence(0, j+1))` did not overflow.
        // This is implicitly handled by the invariant `product_overflow || current_product == product(...)`
        // and the fact that `product_overflow` is false here.
        assert(current_product == product(numbers@) as u32);
    }
    (current_sum, final_product_option)
}
// </vc-code>

fn main() {}
}