// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no changes needed */
spec fn is_nondecreasing(s: Seq<int>) -> bool {
    forall|p: int, q: int| 0 <= p < q < s.len() ==> s[p] <= s[q]
}

proof fn find_k(s: Seq<int>, x: int) -> (k: nat)
    requires 
        forall|p: int, q: int| 0 <= p < q < s.len() ==> s[p] <= s[q],
    ensures 
        0 <= k <= s.len(),
        forall|i: int| 0 <= i < k ==> s[i] <= x,
        forall|i: int| k <= i < s.len() ==> s[i] >= x,
{
    let mut low: nat = 0;
    let mut high: nat = s.len();
    while low < high
        invariant
            (forall|p: int, q: int| 0 <= p < q < s.len() ==> s[p] <= s[q]),
            0 <= low <= high <= s.len(),
            forall|i: int| 0 <= i < low ==> s[i] <= x,
            forall|i: int| high <= i < s.len() ==> s[i] >= x,
        decreases high - low
    {
        let mid = low + (high - low) / 2;
        if s[mid as int] <= x {
            low = mid + 1;
        } else {
            high = mid;
        }
    }
    low
}
// </vc-helpers>

// <vc-spec>
fn search(s: Seq<int>, x: int) -> (k: usize)

    requires 
        forall|p: int, q: int| 0 <= p < q < s.len() ==> s[p] <= s[q],
    ensures 
        0 <= k <= s.len(),
        forall|i: int| 0 <= i < k ==> s[i] <= x,
        forall|i: int| k <= i < s.len() ==> s[i] >= x,
        forall|z: int| s.subrange(0, k as int).contains(z) ==> z <= x,
        forall|z: int| s.subrange(k as int, s.len() as int).contains(z) ==> z >= x,
        s == s.subrange(0, k as int).add(s.subrange(k as int, s.len() as int)),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed compilation error by using the correct lemma vstd::seq::lemma_subrange_split */
{
    let ghost k_nat = find_k(s, x);
    let k = k_nat as usize;

    proof {
        vstd::seq::lemma_subrange_split(s, k as int);
    }

    k
}
// </vc-code>

}
fn main() {}