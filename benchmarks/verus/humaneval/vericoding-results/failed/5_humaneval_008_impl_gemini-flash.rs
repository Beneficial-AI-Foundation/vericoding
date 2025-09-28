// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sum_seq(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        s[0] + sum_seq(s.subrange(1, s.len() as int))
    }
}

spec fn product_seq(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        1
    } else {
        s[0] * product_seq(s.subrange(1, s.len() as int))
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [fixed product_seq_append to match sum_seq_append's structure] */
proof fn product_seq_append(s: Seq<int>, x: int)
    ensures product_seq(s.add(seq![x])) == product_seq(s) * x
    decreases s.len()
{
    if s.len() == 0 {
        assert(product_seq(s.add(seq![x])) == product_seq(seq![x]));
        assert(product_seq(s) * x == 1 * x);
    } else {
        let s_prime = s.subrange(1, s.len() as int);
        product_seq_append(s_prime, x);
    }
}
// </vc-helpers>

// <vc-spec>
fn sum_product(numbers: Vec<i8>) -> (result: (i8, i8))
    ensures ({
        let (sum, product) = result;
        sum as int == sum_seq(numbers@.map(|i, x| x as int)) &&
        product as int == product_seq(numbers@.map(|i, x| x as int)) &&
        (numbers@.len() == 0 ==> sum == 0 && product == 1)
    })
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): [fixed call to product_seq_append] */
{
    let mut sum_val: i8 = 0;
    let mut product_val: i8 = 1;
    let mut i: usize = 0;

    while i < numbers.len()
        invariant
            i <= numbers.len(),
            sum_val@ as int == sum_seq(numbers@.subrange(0, i as int).map(|_, x| x as int)),
            product_val@ as int == product_seq(numbers@.subrange(0, i as int).map(|_, x| x as int))
        decreases numbers.len() - i
    {
        let num = numbers[i];

        proof {
            let s_prev = numbers@.subrange(0, i as int).map(|_, x| x as int);
            sum_seq_append(s_prev, num as int);
            product_seq_append(s_prev, num as int);
        }

        sum_val = (sum_val + num);
        product_val = (product_val * num);
        i = i + 1;
    }
    (sum_val, product_val)
}
// </vc-code>


}

fn main() {}