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
spec fn no_overflow(numbers: Vec<u32>) -> bool {
    sum(numbers@) <= u64::MAX as int
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
fn sum_product(numbers: Vec<u32>) -> (result: (u64, Option<u32>))
    requires
        no_overflow(numbers),
        numbers.len() < u32::MAX,
    ensures
        result.0 == sum(numbers@),
        result.1 matches Some(v) ==> v == product(numbers@),
{
    let num_seq = numbers@;
    let mut sum = 0u64;
    let mut seen_zero = false;
    let mut result_prod = Some(1u32);
    let mut i = 0;
    while i < numbers.len()
        invariant
            0 <= i <= numbers.len(),
            sum as int == sum(num_seq.take(i as int)),
            (!seen_zero ==> (result_prod matches Some(p) ==> p as int == product(num_seq.take(i as int))),
                             result_prod is None ==> product(num_seq.take(i as int)) > u32::MAX as int),
            (seen_zero ==> product(num_seq.take(i as int)) == 0),
            (seen_zero ==> exists |j: int| 0 <= j < i && num_seq@j == 0),
        ensures
            seen_zero ==> product(num_seq.take(i as int)) == 0,
    {
        let val = numbers[i];
        sum += val as u64;
        if val == 0 {
            seen_zero = true;
        }
        if !seen_zero {
            if let Some(p) = result_prod {
                if let Some(new_p) = p.checked_mul(val) {
                    result_prod = Some(new_p);
                } else {
                    result_prod = None;
                }
            }
        }
        i += 1;
    }
    assert(sum as int == sum(num_seq));
    assert(!seen_zero == !seen_zero);
    let result_product = if seen_zero { Some(0) } else { result_prod };
    (sum, result_product)
}
// </vc-code>

fn main() {}
}