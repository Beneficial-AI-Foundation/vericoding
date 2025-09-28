// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): expose definition of max_usize for use in proofs */
proof fn lemma_max_usize_def(a: usize, b: usize)
    ensures
        max_usize(a, b) == (if a >= b { a } else { b }),
{
}

/* helper modified by LLM (iteration 5): if either argument is > 0 then max_usize is > 0 */
proof fn lemma_max_pos_if_either_pos(a: usize, b: usize)
    ensures
        (a > 0 || b > 0) ==> max_usize(a, b) > 0,
{
    if a > 0 || b > 0 {
        if a >= b {
            assert(max_usize(a, b) == a);
            assert(max_usize(a, b) > 0);
        } else {
            assert(max_usize(a, b) == b);
            assert(max_usize(a, b) > 0);
        }
    }
}

/* helper modified by LLM (iteration 5): relate spec f32_add to executable + on f32 */
proof fn lemma_f32_add_is_plus(a: f32, b: f32)
    ensures
        f32_add(a, b) == a + b,
{
}

// </vc-helpers>

// <vc-spec>
spec fn evaluate_laguerre_polynomial(coeffs: Seq<f32>, x: f32) -> f32
{
    arbitrary()
}

spec fn f32_add(a: f32, b: f32) -> f32
{
    arbitrary()
}

spec fn max_usize(a: usize, b: usize) -> usize
{
    if a >= b { a } else { b }
}

fn lagadd(c1: Vec<f32>, c2: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == max_usize(c1.len(), c2.len()),
        forall|i: int| 0 <= i < result.len() ==> {
            #[trigger] result[i] == f32_add(
                if i < c1.len() { c1[i] } else { 0.0f32 },
                if i < c2.len() { c2[i] } else { 0.0f32 }
            )
        },
        (c1.len() > 0 || c2.len() > 0) ==> result.len() > 0
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute values with + and use lemma to relate to spec f32_add without calling it */
    let n = if c1.len() >= c2.len() { c1.len() } else { c2.len() };
    let mut res: Vec<f32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            res.len() == i,
            forall|j: int| 0 <= j < i ==> {
                #[trigger] res[j] == f32_add(
                    if j < c1.len() { c1[j] } else { 0.0f32 },
                    if j < c2.len() { c2[j] } else { 0.0f32 }
                )
            },
        decreases (n as int) - (i as int)
    {
        let v1 = if i < c1.len() { c1[i] } else { 0.0f32 };
        let v2 = if i < c2.len() { c2[i] } else { 0.0f32 };
        let val: f32 = v1 + v2;
        let old_i = i;
        res.push(val);
        proof {
            lemma_f32_add_is_plus(v1, v2);
            assert(res[old_i as int] == val);
            assert(res[old_i as int] == f32_add(v1, v2));
        }
        i += 1;
    }
    let result = res;
    assert(result.len() == n);
    proof { lemma_max_usize_def(c1.len(), c2.len()); }
    if c1.len() >= c2.len() {
        assert(n == max_usize(c1.len(), c2.len()));
    } else {
        assert(n == max_usize(c1.len(), c2.len()));
    }
    if c1.len() > 0 || c2.len() > 0 {
        proof { lemma_max_pos_if_either_pos(c1.len(), c2.len()); }
        assert(result.len() > 0);
    }
    result
}
// </vc-code>

}
fn main() {}