// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sum_r(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        sum_r(s.subrange(0, s.len() - 1)) + s[s.len() - 1]
    }
}

spec fn sum_l(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        s[0] + sum_l(s.subrange(1, s.len() as int))
    }
}

spec fn sum_v(v: Seq<int>, c: int, f: int) -> int {
    if 0 <= c <= f <= v.len() {
        sum_r(v.subrange(c, f))
    } else {
        0
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): retained helper lemma for loop invariant proof */
proof fn lemma_sum_subrange(s: Seq<int>, i: int)
    requires 0 <= i < s.len()
    ensures sum_r(s.subrange(0, i + 1)) == sum_r(s.subrange(0, i)) + s[i]
{
}
// </vc-helpers>

// <vc-spec>
fn sum_elems(v: &[i32]) -> (sum: i32)
ensures sum as int == sum_r(v@.map(|i, x| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Corrected syntax for ghost variable declaration from 'ghost let' to 'let ghost'. */
    let mut i: usize = 0;
    let mut sum: i32 = 0;
    let ghost spec_v = v@.map(|_idx, x| x as int);
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            sum as int == sum_r(spec_v.subrange(0, i as int)),
        decreases v.len() - i
    {
        proof {
            lemma_sum_subrange(spec_v, i as int);
        }
        sum = sum + v[i];
        i = i + 1;
    }
    sum
}
// </vc-code>

}
fn main() {}