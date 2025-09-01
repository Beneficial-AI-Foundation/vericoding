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
    let l = numbers.len();
    let mut sum_int: int = 0;
    let mut prod_int: int = 1;
    let mut overflow = false;

    for i in 0..l {
        sum_int = sum_int + (numbers[i] as int);
        let next_prod = prod_int * (numbers[i] as int);
        if next_prod > (u32::MAX as int) {
            overflow = true;
            prod_int = next_prod;
        } else {
            prod_int = next_prod;
        }
    }

    let result_sum = sum_int as u64;
    let result_prod = if overflow { None } else { Some(prod_int as u32) };
    (result_sum, result_prod)
}
// </vc-code>

fn main() {}
}