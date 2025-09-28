// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): relate exec and ghost indexing for Vec under bounds */
proof fn lemma_index_agree<T>(v: &Vec<T>, i: int)
    requires
        0 <= i < v.len() as int,
    ensures
        v[i] == v@[i],
{
    assert(v[i] == v@[i]);
}
// </vc-helpers>

// <vc-spec>
fn hermemulx(c: Vec<f64>) -> (result: Vec<f64>)
    requires c.len() >= 0,
    ensures
        result.len() == c.len() + 1,
        result[0] == 0.0,
        forall|i: int| 1 <= i < c.len() as int ==> result[i + 1] == c[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): construct result by prefixing 0.0 and copying c; use implies in quantified proof */
    let mut res: Vec<f64> = Vec::new();
    res.push(0.0f64);
    let mut i: usize = 0;
    while i < c.len()
        invariant
            i as int <= c.len() as int,
            res.len() == i + 1,
            res@[0] == 0.0f64,
            forall|k: int| 0 <= k < i as int ==> res@[k + 1] == c@[k],
        decreases (c.len() - i) as int
    {
        let v: f64 = c[i];
        res.push(v);
        proof {
            assert(res@[i as int + 1] == v);
            assert(v == c@[i as int]);
        }
        i = i + 1;
    }
    proof {
        assert(i == c.len());
        assert(res.len() == c.len() + 1);
        assert(0 < res.len());
        assert(res[0] == res@[0]);
        assert(res[0] == 0.0f64);
        assert forall|j: int| 1 <= j < c.len() as int implies res[j + 1] == c[j] by {
            if 1 <= j && j < c.len() as int {
                assert(0 <= j);
                assert(j < c.len() as int);
                assert(j + 1 < res.len() as int) by {
                    assert(res.len() as int == c.len() as int + 1);
                };
                assert(j < i as int);
                assert(res@[j + 1] == c@[j]);
                assert(res[j + 1] == res@[j + 1]);
                assert(c[j] == c@[j]);
            }
        };
    }
    res
}
// </vc-code>

}
fn main() {}