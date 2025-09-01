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
fn sum_product(numbers: Vec<u32>) -> (result: (u64, Option<u32>))
    requires
        numbers.len() < u32::MAX,
    ensures
        result.0 == sum(numbers@),
        result.1 matches Some(v) ==> v == product(numbers@),
{
    let num_seq = numbers@;
    let mut sum: u64 = 0;
    let mut seen_zero = false;
    let mut prod: Option<u32> = Some(1);
    let mut i: usize = 0;
    while i < numbers.len()
        invariant
            0 <= i <= numbers.len(),
            sum as int == sum(num_seq.take(i as int)),
            (!seen_zero ==> (prod matches Some(p) ==> p as int == product(num_seq.take(i as int)),
                             prod is None ==> product(num_seq.take(i as int)) > u32::MAX as int)),
            (seen_zero ==> product(num_seq.take(i as int)) == 0),
            (seen_zero ==> exists |j: int| 0 <= j < i && num_seq[j as int] == 0),
    {
        let val = numbers[i];
        sum += val as u64;
        if val == 0 {
            seen_zero = true;
        }
        if !seen_zero {
            if let Some(p) = prod {
                if let Some(new_p) = p.checked_mul(val) {
                    prod = Some(new_p);
                } else {
                    prod = None;
                }
            }
        }
        i += 1;
    }
    if seen_zero {
        (sum, Some(0))
    } else {
        (sum, prod)
    }
}
// </vc-code>

fn main() {}
}