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
    tracked mut sum_tracked: int = 0;
    tracked mut prod_tracked: int = 1;
    let mut sum_u64: u64 = 0;
    let mut prod_u128: u128 = 1;
    let mut overflow = false;

    for i in 0..l
        //invariant
        requires
            prod_tracked == product(numbers@[0..i]),
            sum_tracked == sum(numbers@[0..i]),
            old(sum_tracked) <= sum_tracked,
            old(prod_tracked) <= prod_tracked,
        ensures
            sum_tracked == old(sum_tracked) + (numbers@[*i] as int),
            prod_tracked == old(prod_tracked) * (numbers@[*i] as int),
    // invariant-end
    {
        proof { sum_tracked = sum_tracked + (numbers@[i] as int); }
        proof { prod_tracked = prod_tracked * (numbers@[i] as int); }
        if prod_tracked > (u32::MAX as int) {
            overflow = true;
        }

        sum_u64 = sum_u64 + (numbers[i] as u64);
        if !overflow {
            if let Some(np_u128) = prod_u128.checked_mul(numbers[i] as u128) {
                prod_u128 = np_u128;
            } else {
                overflow = true;
            }
        }
    }

    proof {
        assert(sum_u64 as int == sum_tracked == sum(numbers@));
        if !overflow {
            assert(prod_u128 as int == prod_tracked);
            assert(prod_tracked <= (u32::MAX as int));
        }
    }
    let result_sum = sum_u64;
    let result_prod = if overflow { None } else { Some(prod_u128 as u32) };
    (result_sum, result_prod)
}
// </vc-code>

fn main() {}
}