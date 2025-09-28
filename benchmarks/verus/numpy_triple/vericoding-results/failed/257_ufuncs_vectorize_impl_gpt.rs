// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): retain existence lemma for f(a) images */
proof fn lemma_exists_f_image<A, B>(f: spec_fn(A) -> B, a: A)
    ensures
        exists|b: B| equal(b, f(a)),
{
    assert(exists|b: B| equal(b, f(a))) by {
        let w = f(a);
        assert(equal(w, f(a)));
    };
}
// </vc-helpers>

// <vc-spec>
fn vectorize<A, B>(f: spec_fn(A) -> B, arr: Vec<A>) -> (result: Vec<B>)
    ensures
        result.len() == arr.len(),
        forall|i: int| 0 <= i < arr.len() ==> result[i] == f(arr[i])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): eliminate choose and compute element via f(a_i) directly */
    let n: usize = arr.len();
    let mut res: Vec<B> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i as int,
            i <= n,
            res.len() == i,
            forall|j: int| 0 <= j < i as int ==> equal(res@[j], f(arr@[j])),
        decreases n - i
    {
        let a_i: A = arr[i];
        let b: B = f(a_i);
        res.push(b);
        proof {
            assert(0 <= i as int);
            assert(i + 1 == res.len());
            assert(equal(res@[i as int], b));
            assert(equal(b, f(a_i)));
            assert(equal(b, f(arr@[i as int])));
        }
        i = i + 1;
    }
    res
}
// </vc-code>

}
fn main() {}