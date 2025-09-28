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
/* helper modified by LLM (iteration 3): kept recursive proof for sum lemma */
proof fn sum_seq_append(s: Seq<int>, x: int)
    ensures sum_seq(s.push(x)) == sum_seq(s) + x
    decreases s.len()
{
    if s.len() > 0 {
        sum_seq_append(s.subrange(1, s.len() as int), x);
    }
}

/* helper modified by LLM (iteration 3): kept recursive proof for product lemma */
proof fn product_seq_append(s: Seq<int>, x: int)
    ensures product_seq(s.push(x)) == product_seq(s) * x
    decreases s.len()
{
    if s.len() > 0 {
        product_seq_append(s.subrange(1, s.len() as int), x);
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
/* code modified by LLM (iteration 3): fixed compilation error (ghost let -> let ghost) */
{
    let mut sum: i64 = 0;
    let mut product: i64 = 1;
    let mut i: usize = 0;

    let ghost int_seq = numbers@.map(|_idx, val| val as int);

    while i < numbers.len()
        invariant
            0 <= i <= numbers.len(),
            sum as int == sum_seq(int_seq.subrange(0, i as int)),
            product as int == product_seq(int_seq.subrange(0, i as int)),
        decreases numbers.len() - i
    {
        let x_i8 = numbers[i];
        sum = sum + (x_i8 as i64);
        product = product * (x_i8 as i64);

        proof {
            let prev_sub_seq = int_seq.subrange(0, i as int);
            let x_int = x_i8 as int;
            assert(int_seq.subrange(0, (i + 1) as int) == prev_sub_seq.push(x_int));
            sum_seq_append(prev_sub_seq, x_int);
            product_seq_append(prev_sub_seq, x_int);
        }

        i = i + 1;
    }

    (sum as i8, product as i8)
}
// </vc-code>


}

fn main() {}