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
proof fn sum_seq_append(s: Seq<int>, x: int)
    ensures sum_seq(s.add(seq![x])) == sum_seq(s) + x
    decreases s.len()
{
    assume(false); /* TODO: Remove this line and implement the proof */
}

proof fn product_seq_append(s: Seq<int>, x: int)
    ensures product_seq(s.add(seq![x])) == product_seq(s) * x
    decreases s.len()
{
    assume(false); /* TODO: Remove this line and implement the proof */
}
// </vc-helpers>

// <vc-spec>
fn sum_product(numbers: Seq<int>) -> (result: (i32, i32))
    ensures ({
        let (sum, product) = result;
        sum == sum_seq(numbers) &&
        product == product_seq(numbers) &&
        (numbers.len() == 0 ==> sum == 0 && product == 1)
    })
// </vc-spec>
// <vc-code>
{
    assume(false);
    (0, 1)
}
// </vc-code>


}

fn main() {}