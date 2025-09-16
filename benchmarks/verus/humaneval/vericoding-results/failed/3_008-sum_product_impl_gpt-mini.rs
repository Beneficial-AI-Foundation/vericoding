// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sum(numbers: Seq<u32>) -> (result:int) {
    numbers.fold_left(0, |acc: int, x| acc + x)
}

spec fn product(numbers: Seq<u32>) -> (result:int) {
    numbers.fold_left(1, |acc: int, x| acc * x)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): seq_sum_u64 returns the sequence sum as u64 */
spec fn seq_sum_u64(numbers: Seq<u32>) -> u64 { sum(numbers) as u64 }

/* helper modified by LLM (iteration 5): seq_product_option_u32 returns Some(product) if within u32 bounds else None */
spec fn seq_product_option_u32(numbers: Seq<u32>) -> Option<u32> { if product(numbers) <= (u32::MAX as int) { Some(product(numbers) as u32) } else { None } }

/* helper modified by LLM (iteration 5): proof linking seq_sum_u64 to spec sum */
proof fn seq_sum_u64_eq_spec_sum(numbers: Seq<u32>)
    ensures
        seq_sum_u64(numbers) == sum(numbers) as u64,
{
    proof {
        assert(seq_sum_u64(numbers) == sum(numbers) as u64);
    }
}

/* helper modified by LLM (iteration 5): proof linking seq_product_option_u32 to spec product when Some */
proof fn seq_product_option_eq(numbers: Seq<u32>)
    ensures
        seq_product_option_u32(numbers) matches Some(v) ==> v as int == product(numbers),
{
    proof {
        match seq_product_option_u32(numbers) {
            Some(v) => { assert(v as int == product(numbers)); }
            None => {}
        }
    }
}

// </vc-helpers>

// <vc-spec>
fn sum_product(numbers: Vec<u32>) -> (result: (u64, Option<u32>))

    requires
        numbers.len() < u32::MAX,

    ensures
        result.0 == sum(numbers@),
        result.1 matches Some(v) ==> v == product(numbers@),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): corrected nat indices, seq slicing and maintained product invariant */
    let seq: Seq<u32> = numbers@;
    let n: nat = seq.len();
    let mut i: nat = 0;
    let mut sum_acc: u64 = 0u64;
    let mut prod_acc: u128 = 1u128;
    let mut fits: bool = true;
    while i < n
        invariant
            i <= n,
            sum_acc == seq_sum_u64(seq[..i]),
            prod_acc == (product(seq[..i]) as u128),
        decreases n - i
    {
        let x: u32 = seq@[i];
        sum_acc = sum_acc + (x as u64);
        prod_acc = prod_acc * (x as u128);
        if prod_acc <= u128::from(u32::MAX) {
            fits = true;
        } else {
            fits = false;
        }
        i = i + 1;
    }
    let opt: Option<u32> = if fits { Some(prod_acc as u32) } else { None };
    proof {
        seq_sum_u64_eq_spec_sum(seq);
        assert(sum_acc == seq_sum_u64(seq[..n]));
        assert(sum_acc as int == sum(seq));
        assert(prod_acc == (product(seq[..n]) as u128));
        match opt {
            Some(v) => {
                assert(v == prod_acc as u32);
                assert(v as int == product(seq));
            }
            None => {}
        }
    }
    (sum_acc, opt)
}
// </vc-code>

}
fn main() {}