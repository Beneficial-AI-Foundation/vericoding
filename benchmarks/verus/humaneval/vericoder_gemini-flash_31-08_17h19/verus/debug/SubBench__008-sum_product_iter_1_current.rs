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

    // Sum of `numbers.len()` elements, each at most U32_MAX, is at most `numbers.len() * U32_MAX`.
    // Since `numbers.len() < u32::MAX` (from preamble), `numbers.len() <= (u32::MAX - 1)`.
    // So the maximum sum is (u32::MAX - 1) * u32::MAX.
    // This value is approximately (2^32 - 1) * (2^32), which is less than 2^64.
    // Specifically, (2^32 - 1) * (2^32) = 2^64 - 2^32, which is less than u64::MAX.
    // u64::MAX = 2^64 - 1.

    // A more formal proof:
    // We know numbers.len() < u32::MAX implies numbers.len() as int <= u32::MAX as int - 1.
    // sum(numbers) <= numbers.len() as int * U32_MAX_AS_INT.
    // If numbers.len() is 0, sum is 0, which fits u64.
    // If numbers.len() >= 1:
    // sum(numbers) <= (u32::MAX as int - 1) * (u32::MAX as int)
    // sum(numbers) <= (0xFFFFFFFF as int - 1) * 0xFFFFFFFF as int
    // sum(numbers) <= 0xFFFFFFFE * 0xFFFFFFFF
    // This product is less than (2^32) * (2^32) = 2^64.
    // Since u64::MAX = 2^64 - 1, the product fits within u64.
    if numbers.len() > 0 {
        assert(sum(numbers) <= (numbers.len() as int) * (U32_MAX_AS_INT as int));
        assert((numbers.len() as int) * (U32_MAX_AS_INT as int) <= (u32::MAX as int - 1) * (U32_MAX_AS_INT as int));
        assert((u32::MAX as int - 1) * (U32_MAX_AS_INT as int) < (u64::MAX as int)); // By arithmetic
    }
    assert(sum(numbers) <= (u64::MAX as int));
}

// Proof method to show that the product of u32s up to 20 elements fits into u32.
// Product becomes very large very quickly.
// For numbers.len() = 0, product is 1. (fits)
// For numbers.len() = 1, product is numbers[0]. (fits if numbers[0] is u32)
// For numbers.len() = 2, max product is u32::MAX * u32::MAX, which is (2^32-1) * (2^32-1) approx 2^64. (does not fit)
// The problem statement says `Option<u32>` for product, implying it might not fit.
// Thus, this lemma is not generally useful. The code needs to check for overflow (and it does not need to if it returns Option<u32>).
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
        current_sum == sum(numbers.subsequence(0, i)) as u64,
        product_overflow || current_product == product(numbers.subsequence(0, i)) as u32,
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
        lemma_sum_u32_fits_u64(numbers.subsequence(0, i)),
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

    assert(current_sum == sum(numbers@) as u64);

    let final_product_option: Option<u32>;
    if product_overflow {
        final_product_option = None;
    } else {
        final_product_option = Some(current_product);

        // Prove that if not overflowed, current_product is the actual product
        assert(current_product == product(numbers@) as u32);
    }
    (current_sum, final_product_option)
}
// </vc-code>

fn main() {}
}