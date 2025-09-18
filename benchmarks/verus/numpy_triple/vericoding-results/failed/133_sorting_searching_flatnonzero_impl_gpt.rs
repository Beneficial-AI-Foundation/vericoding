// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): define predicate for strict increase over Seq<usize> */
spec fn strictly_increasing(s: Seq<usize>) -> bool { forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] < s[j] }

/* helper modified by LLM (iteration 2): lemma that pushing a larger element preserves strict increase */
proof fn lemma_strict_incr_push(s: Seq<usize>, x: usize)
    requires
        strictly_increasing(s),
        forall|p: int| 0 <= p < s.len() ==> s[p] < x
    ensures
        strictly_increasing(s.push(x))
{
    assert(forall|i: int, j: int|
        0 <= i < j < s.push(x).len()
        ==> s.push(x)[i] < s.push(x)[j]
    ) by {
        let sl = s.len();
        if j < sl {
            assert(0 <= i < j < sl);
            assert(s.push(x)[i] == s[i]);
            assert(s.push(x)[j] == s[j]);
            assert(s[i] < s[j]);
        } else {
            assert(j == sl);
            assert(0 <= i < sl);
            assert(s.push(x)[i] == s[i]);
            assert(s.push(x)[j] == x);
            assert(s[i] < x);
        }
    };
}
// </vc-helpers>

// <vc-spec>
fn flatnonzero(a: Vec<f64>) -> (result: Vec<usize>)
    ensures

        forall|i: int| 0 <= i < result.len() ==> a[result[i] as int] != 0.0,

        forall|j: int| 0 <= j < a.len() && a[j] != 0.0 ==> exists|k: int| 0 <= k < result.len() && result[k] == j,

        forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result.len() && i != j ==> result[i] != result[j],

        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] < result[j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): implement scanning loop, use usize indexing, and maintain invariants with proofs */
    let mut result: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            forall|p: int| 0 <= p < result.len() as int ==> a@[result@[p] as int] != 0.0,
            forall|p: int| 0 <= p < result.len() as int ==> result@[p] < i,
            strictly_increasing(result@),
            forall|j: int| 0 <= j < i as int && a@[j] != 0.0 ==> exists|k: int| 0 <= k < result.len() as int && result@[k] as int == j
        decreases a.len() - i
    {
        if a[i] != 0.0 {
            let old_len = result.len();
            proof {
                assert(strictly_increasing(result@));
                lemma_strict_incr_push(result@, i);
            }
            result.push(i);
            proof {
                assert(old_len as int >= 0);
                assert(old_len + 1 == result.len());
                assert(0 <= old_len as int && old_len as int < result.len() as int);
                assert(result@[old_len as int] == i);
                assert(a@[i as int] == a[i]);
            }
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}