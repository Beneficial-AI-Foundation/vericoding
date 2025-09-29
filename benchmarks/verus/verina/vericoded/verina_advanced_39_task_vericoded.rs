// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): provide a trivial helper proof function (unused) */
proof fn helper_placeholder() { }
// </vc-helpers>

// <vc-spec>
fn max_of_list(lst: &Vec<usize>) -> (result: usize)
    requires lst.len() > 0,
    ensures
        exists|i: int| 0 <= i < lst.len() && lst[i] == result,
        forall|i: int| 0 <= i < lst.len() ==> lst[i] <= result,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fix spec indexing type mismatch and add proof for existential ensures */
    let n = lst.len();
    let mut idx: usize = 0;
    let mut i: usize = 1;
    while i < n
        invariant
            1 <= i,
            i <= n,
            idx < i,
            n == lst.len(),
            forall|j: int| 0 <= j && j < i as int ==> lst[j] <= lst[idx as int],
        decreases (n as int - i as int)
    {
        if lst[i] > lst[idx] {
            idx = i;
        }
        i += 1;
    }
    let result0 = lst[idx];
    proof {
        assert(i >= n);
        assert(i == n);
        assert(idx < lst.len());
        let w: int = idx as int;
        assert(0 <= w && w < lst.len() as int);
        assert(lst[w] == result0);
        assert(exists|k: int| 0 <= k && k < lst.len() as int && lst[k] == result0);
    }
    result0
}
// </vc-code>

}
fn main() {}