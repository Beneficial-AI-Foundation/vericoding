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
/* helper modified by LLM (iteration 4): fixed invariant syntax in proof */
proof fn sum_seq_append(s: Seq<int>, x: int)
    ensures sum_seq(s.add(seq![x])) == sum_seq(s) + x
    decreases s.len()
{
    if s.len() == 0 {
        assert(sum_seq(seq![x]) == x);
        assert(sum_seq(s) == 0);
    } else {
        let s0 = s[0];
        let s_prime = s.subrange(1, s.len() as int);
        sum_seq_append(s_prime, x);
        assert(s.add(seq![x]) == seq![s0].add(s_prime.add(seq![x])));
        assert(sum_seq(s.add(seq![x])) == s0 + sum_seq(s_prime.add(seq![x])));
        assert(sum_seq(s_prime.add(seq![x])) == sum_seq(s_prime) + x);
        assert(sum_seq(s.add(seq![x])) == s0 + (sum_seq(s_prime) + x));
        assert(sum_seq(s) == s0 + sum_seq(s_prime));
    }
}

/* helper modified by LLM (iteration 4): fixed invariant syntax in proof */
proof fn product_seq_append(s: Seq<int>, x: int)
    ensures product_seq(s.add(seq![x])) == product_seq(s) * x
    decreases s.len()
{
    if s.len() == 0 {
        assert(product_seq(seq![x]) == x);
        assert(product_seq(s) == 1);
    } else {
        let s0 = s[0];
        let s_prime = s.subrange(1, s.len() as int);
        product_seq_append(s_prime, x);
        assert(s.add(seq![x]) == seq![s0].add(s_prime.add(seq![x])));
        assert(product_seq(s.add(seq![x])) == s0 * product_seq(s_prime.add(seq![x])));
        assert(product_seq(s_prime.add(seq![x])) == product_seq(s_prime) * x);
        assert(product_seq(s.add(seq![x])) == s0 * (product_seq(s_prime) * x));
        assert(product_seq(s) == s0 * product_seq(s_prime));
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
/* code modified by LLM (iteration 5): fixed invariant block syntax */
{
    let mut sum_int: int = 0;
    let mut product_int: int = 1;
    let mut i: int = 0;
    let n = numbers.len() as int;
    while i < n
        invariant
            0 <= i <= n,
            sum_int == sum_seq(numbers@.subrange(0, i)),
            product_int == product_seq(numbers@.subrange(0, i)),
        decreases n - i
    {
        let x = numbers@[i] as int;
        sum_int = sum_int + x;
        product_int = product_int * x;
        i = i + 1;
    }
    let sum_i8 = sum_int as i8;
    let product_i8 = product_int as i8;
    (sum_i8, product_i8)
}
// </vc-code>


}

fn main() {}