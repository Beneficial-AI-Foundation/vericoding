// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixing decreases clause syntax. */
spec fn mult_poly(a: Seq<f32>, b: Seq<f32>) -> Seq<f32>
    decreases a.len(), b.len()
{
    if a.len() == 0 || b.len() == 0 {
        Seq::empty()
    } else {
        let mut result = Seq::<f32>::new( (a.len() + b.len() - 1) as nat, |i: nat| 0.0f32);
        for i in 0..a.len() {
            for j in 0..b.len() {
                result = result.update((i + j) as nat, result.index( (i + j) as nat) + a.index(i as nat) * b.index(j as nat));
            }
        }
        result
    }
}
// </vc-helpers>

// <vc-spec>
fn polypow(c: Vec<f32>, pow: nat) -> (result: Vec<f32>)
    ensures
        pow == 0 ==> (result.len() == 1 && result[0] == 1.0f32),
        pow == 1 ==> result.len() == c.len() && (forall|i: int| 0 <= i < c.len() ==> result[i] == c[i]),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixing `nat` and `int` usage in `c_seq` creation and `res_vec` population. `c.len()` becomes `c@.len()` to get the ghost length, and indexing accesses `int`. The `res_seq.index` is also corrected to use an `int` for the argument. */
{
    let c_seq = Seq::new(c@.len() as nat, |i: nat| c@[i as int]);

    if pow == 0 {
        let res_vec = vec![1.0f32];
        proof {
            assert(res_vec.len() == 1);
            assert(res_vec[0] == 1.0f32);
        }
        res_vec
    } else if pow == 1 {
        proof {
            forall |i: int| {
                if 0 <= i && i < c.len() {
                   assert(c@[i] == c@[i]);
                }
            }
        }
        c
    } else {
        let mut res_seq = c_seq;
        let mut k = 1;
        while k < pow
            invariant
                k >= 1,
                k <= pow,
                res_seq.len() >= 0,
        {
            res_seq = mult_poly(res_seq, c_seq);
            k = k + 1;
        }
        let mut res_vec = Vec::new();
        for i in 0..res_seq.len() {
            res_vec.push(res_seq.index(i as int));
        }
        res_vec
    }
}
// </vc-code>

}
fn main() {}