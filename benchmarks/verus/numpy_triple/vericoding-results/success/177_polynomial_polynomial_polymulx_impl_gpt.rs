// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): simple sequence right-shift by one with zero padding */
spec fn shift_right1_seq(s: Seq<f32>) -> Seq<f32> { seq![0.0f32] + s }

/* helper modified by LLM (iteration 3): arithmetic lemma: from 0 <= k < i and i <= n, conclude 0 <= k < n */
proof fn lemma_lt_trans(k: int, i: int, n: int)
    requires
        0 <= k < i,
        i <= n,
    ensures
        0 <= k < n,
{
    assert(0 <= k);
    assert(k < i);
    assert(i <= n);
    assert(k < n);
}
// </vc-helpers>

// <vc-spec>
fn polymulx(c: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == c.len() + 1,
        result[0] == 0.0f32,
        forall|i: int| 0 <= i < c.len() ==> result[i + 1] == c[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): removed problematic quantifier and added trigger; tied n to c.len() for bounds */
    let n: usize = c.len();
    let mut res: Vec<f32> = Vec::new();
    res.push(0.0f32);

    let mut i: usize = 0;
    while i < n
        invariant
            (i as int) <= (n as int),
            (n as int) == c.len(),
            res.len() == (i as int) + 1,
            res@[0] == 0.0f32,
            forall|k: int| 0 <= k < i as int ==> #[trigger] res@[k + 1] == c@[k],
        decreases n - i
    {
        res.push(c[i]);
        i += 1;
    }

    res
}
// </vc-code>

}
fn main() {}