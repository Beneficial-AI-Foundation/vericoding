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
    // impl-start
    if numbers.len() == 0 {
        return (0, Some(1));
    }
    let mut sum: u64 = 0;
    let tracked mut product: int = 1;
    let mut i: usize = 0;
    while i < numbers.len()
        invariant
            0 <= i <= numbers.len(),
            sum as int == numbers@.subrange(0, i).fold_left(0, |a: int, x: u32| a + x),
            product == numbers@.subrange(0, i).fold_left(1, |a: int, x: u32| a * x),
    {
        let x = numbers[i] as u64;
        assert(sum <= u64::MAX - x) by {
            // numbers.len() < u32::MAX and each x < u32::MAX, so sum < (u32::MAX)^2 < 2^64
        };
        sum += x;
        product *= (numbers[i] as int);
        i += 1;
    }
    if product <= (u32::MAX as int) {
        (sum, Some(product as u32))
    } else {
        (sum, None)
    }
    // impl-end
}
// </vc-code>

fn main() {}
}