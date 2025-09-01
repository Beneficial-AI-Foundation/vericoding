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
// No helpers needed for this proof.
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
    let n: usize = numbers.len();
    let mut i: usize = 0;
    let mut sum_acc: u64 = 0;
    let mut prod_acc: u128 = 1;
    let mut prod_ok: bool = true;

    ghost let mut prod_spec: int = 1;

    while i < n
        invariant i <= n
        invariant (sum_acc as int) == sum(numbers@.slice(0, i))
        invariant prod_spec == product(numbers@.slice(0, i))
        invariant prod_ok ==> ((prod_acc as int) == prod_spec && prod_acc <= (u32::MAX as u128))
        decreases n - i
    {
        let x: u32 = numbers[i];
        sum_acc = sum_acc + (x as u64);

        // update the ghost/spec product
        proof {
            prod_spec = prod_spec * (x as int);
        }

        if prod_ok {
            let newp: u128 = prod_acc * (x as u128);
            if newp <= (u32::MAX as u128) {
                prod_acc = newp;
            } else {
                prod_ok = false;
            }
        }

        i += 1;
    }

    if prod_ok {
        proof {
            // At loop exit i == n, so prod_spec == product(numbers@)
            assert(prod_acc <= (u32::MAX as u128));
            assert((prod_acc as int) == prod_spec);
            assert(prod_spec == product(numbers@));
        }
        let v: u32 = prod_acc as u32;
        (sum_acc, Some(v))
    } else {
        (sum_acc, None)
    }
    // impl-end
}
// </vc-code>

fn main() {}
}