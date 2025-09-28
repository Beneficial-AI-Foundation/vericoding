// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): push increases length by 1 and last element equals x */
fn lemma_push_last_i32(mut v: Vec<i32>, x: i32)
    ensures
        v.len() == old(v.len()) + 1,
        v@[(v.len() as int) - 1] == x,
{
    let old_len: usize = v.len();
    v.push(x);
    assert(v.len() == old_len + 1);
    let idx: int = (v.len() as int) - 1;
    assert(0 <= idx && idx < v.len() as int);
    assert(v@[idx] == x);
}

// </vc-helpers>

// <vc-spec>
spec fn all_nonzero(v: Seq<i32>) -> bool {
    forall|i: int| 0 <= i < v.len() ==> v[i] != 0
}

fn mod_vec(a: Vec<i32>, b: Vec<i32>) -> (result: Vec<i32>)
    requires 
        a.len() == b.len(),
        all_nonzero(b@),
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i] % b[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement mod_vec using lemma_push_last_i32 and maintain invariants */
    let n = a.len();
    let mut res: Vec<i32> = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n
        invariant
            res.len() == i,
            forall|j: int| 0 <= j < (i as int) ==> res@[j] == a@[j] % b@[j],
        decreases n - i
    {
        let ai: i32 = a[i];
        let bi: i32 = b[i];
        proof {
            assert(0 <= (i as int));
            assert((i as int) < (b@).len());
            assert(all_nonzero(b@));
            assert(b@[i as int] != 0);
        }
        assert(b@[i as int] != 0);
        let ri: i32 = ai % bi;
        lemma_push_last_i32(res, ri);
        i = i + 1;
    }
    res
}

// </vc-code>


}
fn main() {}