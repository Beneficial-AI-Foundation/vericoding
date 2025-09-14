// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): noop helper kept for auxiliary proofs */
proof fn noop_helper() ensures true { }
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn two_way_sort(a: &mut Vec<bool>)
    requires
        old(a).len() <= 100_000,
    ensures
        a.len() == old(a).len(),
        a@.to_multiset() == old(a)@.to_multiset(),
        forall|i: int, j: int| 0 <= i < j < a.len() ==> !a[i] || a[j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): clone, count falses with precise invariants, fill and prove multiset+sorted */
    let n: usize = a.len();
    let old_vec: Vec<bool> = a.clone();

    let mut i: usize = 0;
    let mut fcount: usize = 0;
    while i < n
        invariant
            i <= n,
            fcount <= n,
            (fcount as nat) == (old_vec@)[0..(i as int)].to_multiset().count(false),
        decreases n - i
    {
        if !old_vec[i] {
            fcount = fcount + 1;
        }
        i = i + 1;
    }

    let mut j: usize = 0;
    while j < n
        invariant
            j <= n,
            fcount <= n,
            forall|k: int| 0 <= k < (j as int) ==> if k < (fcount as int) then !a@[k] else a@[k],
        decreases n - j
    {
        if j < fcount {
            a[j] = false;
        } else {
            a[j] = true;
        }
        j = j + 1;
    }

    proof {
        let old_seq: Seq<bool> = old_vec@;
        assert(a@.len() == old_seq.len());
        assert((fcount as nat) == old_seq.to_multiset().count(false));
        assert(forall|k: int| 0 <= k < a@.len() ==> if k < (fcount as int) then !a@[k] else a@[k]);
        assert(a@.to_multiset().count(false) == (fcount as nat));
        assert(old_seq.to_multiset().count(false) == (fcount as nat));
        assert(a@.to_multiset() == old_seq.to_multiset());
        assert(forall|p: int, q: int| 0 <= p < q < a@.len() ==> !a@[p] || a@[q]);
    }
}

// </vc-code>

}
fn main() {}