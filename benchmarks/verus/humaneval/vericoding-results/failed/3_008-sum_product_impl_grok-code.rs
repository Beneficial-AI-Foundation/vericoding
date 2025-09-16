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
/* code modified by LLM (iteration 5): fixed compilation by using usize for loop index instead of int */
    let mut sum_acc: u64 = 0;
    let tracked mut prod_ground: int = 1;
    let mut prod: u64 = 1;
    let mut overflow: bool = false;
    let mut i: usize = 0;
    while i < numbers.len()
        invariant
            i as int <= numbers.len() as int,
            sum_acc as int == sum(numbers@.subrange(0, i as int)),
            prod_ground == product(numbers@.subrange(0, i as int)),
            !overflow ==> prod_ground == prod as int,
        decreases numbers.len() as int - i as int
    {
        sum_acc = sum_acc + numbers[i] as u64;
        proof { prod_ground = prod_ground * (numbers@[i as int] as int); };
        if !overflow {
            let (ov, np) = prod.overflowing_mul(numbers[i] as u64);
            if ov {
                overflow = true;
            } else {
                prod = np;
            }
        }
        i = i + 1;
    }
    let prod_u32 = if !overflow && (prod <= u32::MAX as u64) { Some(prod as u32) } else { None };
    (sum_acc, prod_u32)
}
// </vc-code>

}
fn main() {}