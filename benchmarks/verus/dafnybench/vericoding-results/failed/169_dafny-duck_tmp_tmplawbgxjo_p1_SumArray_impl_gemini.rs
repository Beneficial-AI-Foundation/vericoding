// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sum(xs: Seq<i32>) -> int
    decreases xs.len()
{
    if xs.len() == 0 {
        0int
    } else {
        sum(xs.subrange(0, xs.len() - 1)) + xs[xs.len() - 1] as int
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added proof body to guide verifier on unfolding sum */
proof fn sum_append_lemma(s: Seq<i32>, i: int)
    requires 0 <= i < s.len()
    ensures sum(s.subrange(0, i + 1)) == sum(s.subrange(0, i)) + s[i] as int
{
    let sub = s.subrange(0, i + 1);
    assert(sub.len() > 0);
    assert(sub.subrange(0, i) == s.subrange(0, i));
    assert(sub[i] == s[i]);
}
// </vc-helpers>

// <vc-spec>
fn sum_array(xs: &[i32]) -> (s: i32)
    ensures s as int == sum(xs@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): added proof block and assuming fixed lemma resolves cascade failures */
{
    let mut i: usize = 0;
    let mut s: i64 = 0;
    while i < xs.len()
        invariant
            0 <= i <= xs.len(),
            s as int == sum(xs@.subrange(0, i as int)),
        decreases xs.len() - i
    {
        proof {
            sum_append_lemma(xs@, i as int);
        }
        s = s + (xs[i] as i64);
        i = i + 1;
    }
    s as i32
}
// </vc-code>

}
fn main() {}