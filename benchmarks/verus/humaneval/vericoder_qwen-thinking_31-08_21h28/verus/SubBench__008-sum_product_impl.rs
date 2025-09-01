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
    let n = numbers.len();
    let mut total_sum = 0u64;
    let mut total_product = 1u32;
    let mut overflow = false;
    let mut i = 0;
    while i < n {
        invariant {
            i <= n,
            total_sum == (sum(numbers@.slice(0, i)) as u64),
            overflow || total_product == (product(numbers@.slice(0, i)) as u32)
        }
        total_sum += numbers@[i] as u64;
        if !overflow {
            if numbers@[i] == 0 {
                total_product = 0;
            } else if total_product > u32::MAX / numbers@[i] {
                overflow = true;
            } else {
                total_product = total_product * numbers@[i];
            }
        }
        i += 1;
    }
    assert!(i == n);
    (total_sum as u64, if overflow { None } else { Some(total_product) })
}
// </vc-code>

fn main() {}
}