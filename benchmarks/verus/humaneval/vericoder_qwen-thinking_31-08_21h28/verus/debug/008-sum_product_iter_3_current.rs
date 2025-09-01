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
    let mut sum = 0u64;
    for i in 0..numbers.len() {
        sum += numbers[i] as u64;
    }

    let n = numbers.len();
    let mut i = 0;
    let mut prod = 1u32;
    let mut overflow = false;
    while i < n {
        invariant
            i <= n
            && (overflow == false ==> (prod as int) == product(numbers@.prefix(i)))
        let num = numbers[i];
        if num != 0 && prod > u32::MAX / num {
            overflow = true;
            break;
        }
        prod = prod * num;
        i = i + 1;
    }

    if overflow {
        (sum, None)
    } else {
        (sum, Some(prod))
    }
}
// </vc-code>

fn main() {}
}