// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): relate usize index bound to int bound */
fn usize_index_as_int(n: usize, i: usize)
    requires
        i < n,
    ensures
        0 <= (i as int) && (i as int) < (n as int),
{
    proof {
        assert((i as int) >= 0);
        assert((i as int) < (n as int));
    }
}

/* helper modified by LLM (iteration 5): get Vec<i8> element and relate to seq view */
fn vec_get_i8(v: &Vec<i8>, i: usize) -> i8
    requires
        i < v.len(),
    ensures
        result == v.view()@[i as int],
{
    let x: i8 = v[i];
    x
}

// </vc-helpers>

// <vc-spec>
fn subtract(a: Vec<i8>, b: Vec<i8>) -> (result: Vec<i8>)
    requires a.len() == b.len(),
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result@[i] == a@[i] - b@[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement elementwise subtraction with invariant proofs */
    let mut res: Vec<i8> = Vec::new();
    let mut i: usize = 0usize;
    let n: usize = a.len();
    while i < n
        invariant
            res.len() == i,
            forall|j: int| 0 <= j < (i as int) ==> res@[j] == a@[j] - b@[j],
        decreases n - i
    {
        proof {
            assert(i < n);
        }
        let ai: i8 = vec_get_i8(&a, i);
        let bi: i8 = vec_get_i8(&b, i);
        let vi: i8 = ai.wrapping_sub(bi);
        res.push(vi);
        proof {
            // after push, res.len() == i + 1 and the last element equals vi
            assert(res.len() == i + 1);
            assert(res@[i as int] == vi);
            assert(a@[i as int] == ai);
            assert(b@[i as int] == bi);
            assert(res@[i as int] == a@[i as int] - b@[i as int]);
        }
        i = i + 1;
    }
    res
}
// </vc-code>


}
fn main() {}