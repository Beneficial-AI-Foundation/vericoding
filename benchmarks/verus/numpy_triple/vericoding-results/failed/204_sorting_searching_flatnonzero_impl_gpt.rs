// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): change sequence element type from nat to usize to match out@ */
proof fn strictly_increasing_implies_distinct_nat(s: Seq<usize>)
    requires
        forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] < s[j],
    ensures
        forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && i != j ==> s[i] != s[j],
{
    assert forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && i != j ==> s[i] != s[j] by {
        if i < j {
            assert(s[i] < s[j]);
        } else {
            assert(j < i);
            assert(s[j] < s[i]);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn flatnonzero(a: Vec<f64>) -> (result: Vec<usize>)
    ensures

        forall|i: int| 0 <= i < result@.len() ==> a[result@[i] as int] != 0.0,

        forall|j: int| 0 <= j < a@.len() && a@[j] != 0.0 ==> exists|k: int| 0 <= k < result@.len() && result@[k] == j,

        forall|i: int, j: int| 0 <= i < result@.len() && 0 <= j < result@.len() && i != j ==> result@[i] != result@[j],

        forall|i: int, j: int| 0 <= i < j < result@.len() ==> result@[i] < result@[j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): maintain invariants and call updated helper on Seq<usize> */
    let n = a.len();
    let mut out: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i as int <= a@.len(),
            forall|t: int| 0 <= t < out@.len() ==> out@[t] < i as int,
            forall|t: int| 0 <= t < out@.len() ==> a[out@[t] as int] != 0.0,
            forall|p: int, q: int| 0 <= p < q < out@.len() ==> out@[p] < out@[q],
            forall|j: int| 0 <= j < i as int && a@[j] != 0.0 ==> exists|k: int| 0 <= k < out@.len() && out@[k] == j,
        decreases a@.len() - i as int
    {
        let j = i;
        proof {
            assert forall|p: int| 0 <= p < out@.len() ==> out@[p] < j as int by {
                assert(out@[p] < i as int);
                assert(i as int == j as int);
            }
        }
        i += 1;
        if a[j] != 0.0 {
            out.push(j);
            proof {
                assert(exists|k: int| 0 <= k < out@.len() && out@[k] == j) by {
                    let k = out@.len() - 1;
                    assert(0 <= k && k < out@.len());
                }
            }
        }
    }
    proof {
        strictly_increasing_implies_distinct_nat(out@);
    }
    out
}
// </vc-code>

}
fn main() {}