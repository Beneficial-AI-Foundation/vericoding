// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): define collection of nonzero indices in prefix and supporting lemmas with full inductive proofs for bounds, membership, ordering, and distinctness */
spec fn collect_nonzero_prefix(a: Seq<f64>, n: nat) -> Seq<usize>
    decreases n
{
    if n == 0 {
        Seq::empty()
    } else {
        let m: nat = ((n - 1) as nat);
        let rest = collect_nonzero_prefix(a, m);
        if a[m as int] != 0.0 {
            rest.push(m as usize)
        } else {
            rest
        }
    }
}

/* helper modified by LLM (iteration 5): unfold one-step relation for n = i + 1 */
proof fn lemma_collect_step(a: Seq<f64>, i: nat)
    requires
        i < a.len()
    ensures
        collect_nonzero_prefix(a, i + 1) ==
            if a[i as int] != 0.0 { collect_nonzero_prefix(a, i).push(i as usize) } else { collect_nonzero_prefix(a, i) }
{
    reveal(collect_nonzero_prefix);
    assert((((i + 1) as int) - 1) == (i as int));
}

/* helper modified by LLM (iteration 5): inductively prove properties of the collected prefix: elements are in-range and nonzero; coverage of all nonzeros; strict ordering and uniqueness */
proof fn lemma_collect_properties(a: Seq<f64>, n: nat)
    requires
        n <= a.len()
    ensures
        forall|k:int| 0 <= k < collect_nonzero_prefix(a, n).len() ==>
            ((collect_nonzero_prefix(a, n)[k] as int) < (n as int)) &&
            a[collect_nonzero_prefix(a, n)[k] as int] != 0.0,
        forall|i:int| 0 <= i < (n as int) && a[i] != 0.0 ==>
            collect_nonzero_prefix(a, n).contains(i as usize),
        forall|i:int, j:int| 0 <= i < j < collect_nonzero_prefix(a, n).len() ==>
            ((collect_nonzero_prefix(a, n)[i] as int) < (collect_nonzero_prefix(a, n)[j] as int)),
        forall|i:int, j:int| 0 <= i < j < collect_nonzero_prefix(a, n).len() ==>
            collect_nonzero_prefix(a, n)[i] != collect_nonzero_prefix(a, n)[j]
    decreases n
{
    if n == 0 {
        reveal(collect_nonzero_prefix);
    } else {
        let m: nat = ((n - 1) as nat);
        lemma_collect_properties(a, m);
        reveal(collect_nonzero_prefix);
        assert((m as int) + 1 == n as int);
        let s = collect_nonzero_prefix(a, m);
        if a[m as int] == 0.0 {
            // collect_nonzero_prefix(a, n) == s
            assert(collect_nonzero_prefix(a, n) == s);

            // Elements are in-range (< n) and nonzero
            assert forall|k:int| 0 <= k < collect_nonzero_prefix(a, n).len() ==> (((collect_nonzero_prefix(a, n)[k] as int) < (n as int)) && a[collect_nonzero_prefix(a, n)[k] as int] != 0.0) by {
                if 0 <= k < s.len() {
                    // From IH on m
                    assert(((s[k] as int) < (m as int)) && a[s[k] as int] != 0.0);
                    assert((s[k] as int) < (n as int));
                }
            };

            // Coverage of nonzeros up to n: same as up to m; i == m cannot satisfy antecedent since a[m]==0
            assert forall|i:int| 0 <= i < (n as int) && a[i] != 0.0 ==> collect_nonzero_prefix(a, n).contains(i as usize) by {
                if 0 <= i < (n as int) && a[i] != 0.0 {
                    if i < (m as int) {
                        // From IH on m
                        assert(s.contains(i as usize));
                        assert(collect_nonzero_prefix(a, n) == s);
                    } else {
                        // Then i == m, but a[m] == 0 contradicts antecedent; vacuous
                    }
                }
            };

            // Strict ordering and uniqueness propagate from IH
            assert forall|i:int, j:int| 0 <= i < j < collect_nonzero_prefix(a, n).len() ==> ((collect_nonzero_prefix(a, n)[i] as int) < (collect_nonzero_prefix(a, n)[j] as int)) by {
                if 0 <= i < j < s.len() {
                    assert(((s[i] as int) < (s[j] as int)));
                }
            };
            assert forall|i:int, j:int| 0 <= i < j < collect_nonzero_prefix(a, n).len() ==> collect_nonzero_prefix(a, n)[i] != collect_nonzero_prefix(a, n)[j] by {
                if 0 <= i < j < s.len() {
                    assert(((s[i] as int) < (s[j] as int)));
                }
            };
        } else {
            // collect_nonzero_prefix(a, n) == s.push(m)
            let t = s.push(m as usize);
            assert(collect_nonzero_prefix(a, n) == t);
            assert(t.len() == s.len() + 1);

            // Elements are in-range (< n) and nonzero
            assert forall|k:int| 0 <= k < collect_nonzero_prefix(a, n).len() ==> (((collect_nonzero_prefix(a, n)[k] as int) < (n as int)) && a[collect_nonzero_prefix(a, n)[k] as int] != 0.0) by {
                if 0 <= k < t.len() {
                    if k < s.len() {
                        // From IH on m for s
                        assert(((s[k] as int) < (m as int)) && a[s[k] as int] != 0.0);
                        assert((s[k] as int) < (n as int));
                        assert(t[k] == s[k]);
                    } else {
                        // Then k == s.len()
                        assert(k >= s.len());
                        assert(k <= s.len());
                        assert(k == s.len());
                        assert(t[k] == (m as usize));
                        assert((m as int) < (n as int));
                        assert(a[m as int] != 0.0);
                    }
                }
            };

            // Coverage of nonzeros up to n
            assert forall|i:int| 0 <= i < (n as int) && a[i] != 0.0 ==> collect_nonzero_prefix(a, n).contains(i as usize) by {
                if 0 <= i < (n as int) && a[i] != 0.0 {
                    if i < (m as int) {
                        // Membership lifts from s to t
                        assert(s.contains(i as usize));
                        // Since for any k < s.len(), t[k] == s[k]
                        // the witness for s also witnesses t
                    } else {
                        // i == m
                        assert(i >= (m as int));
                        assert(i <= (m as int));
                        assert(i == (m as int));
                        // Last element equals m
                        assert(t[s.len()] == (m as usize));
                        // Hence contains holds
                        assert(t.contains((m as usize)));
                    }
                }
            };

            // Strict ordering
            assert forall|i:int, j:int| 0 <= i < j < collect_nonzero_prefix(a, n).len() ==> ((collect_nonzero_prefix(a, n)[i] as int) < (collect_nonzero_prefix(a, n)[j] as int)) by {
                if 0 <= i < j < t.len() {
                    if j < s.len() {
                        // both in s
                        assert(((s[i] as int) < (s[j] as int)));
                        assert(t[i] == s[i]);
                        assert(t[j] == s[j]);
                    } else {
                        // j == s.len(), i < s.len()
                        assert(j >= s.len());
                        assert(j <= s.len());
                        assert(j == s.len());
                        assert(t[j] == (m as usize));
                        // From IH on m: any element of s is < m
                        assert(0 <= i < s.len());
                        assert(((s[i] as int) < (m as int)));
                        assert((t[i] as int) == (s[i] as int));
                        assert((t[i] as int) < (t[j] as int));
                    }
                }
            };

            // Uniqueness (follows from strict ordering)
            assert forall|i:int, j:int| 0 <= i < j < collect_nonzero_prefix(a, n).len() ==> collect_nonzero_prefix(a, n)[i] != collect_nonzero_prefix(a, n)[j] by {
                if 0 <= i < j < t.len() {
                    assert(((t[i] as int) < (t[j] as int)));
                }
            };
        }
    }
}

// </vc-helpers>

// <vc-spec>
fn numpy_argwhere(a: Vec<f64>) -> (indices: Vec<usize>)
    ensures

        forall|i: int| 0 <= i < indices.len() ==> 
            indices[i] < a.len() && a[indices[i] as int] != 0.0,

        forall|i: int| 0 <= i < a.len() && a[i] != 0.0 ==> 
            indices@.contains(i as usize),

        forall|i: int, j: int| 0 <= i < j < indices.len() ==> 
            indices[i] != indices[j],

        forall|i: int, j: int| 0 <= i < j < indices.len() ==> 
            indices[i] < indices[j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement argwhere by scanning with a loop maintaining a precise sequence invariant mapped to collect_nonzero_prefix; fix int/nat bounds and update invariant with step lemma */
    let n: usize = a.len();
    let mut indices: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == a.len(),
            i <= n,
            indices@ == collect_nonzero_prefix(a@, i as nat)
        decreases n - i
    {
        assert(i < a.len());
        if a[i] != 0.0 {
            indices.push(i);
            proof {
                // After push: indices@ == old(indices@).push(i) and old(indices@) == collect_nonzero_prefix(a@, i as nat)
                // Use step lemma to rewrite to the (i+1) prefix
                lemma_collect_step(a@, i as nat);
                assert(indices@ == collect_nonzero_prefix(a@, i as nat).push(i));
                assert(collect_nonzero_prefix(a@, (i as nat) + 1) == collect_nonzero_prefix(a@, i as nat).push(i));
                assert(indices@ == collect_nonzero_prefix(a@, (i as nat) + 1));
            }
        } else {
            proof {
                // No push; the collected prefix does not change when a[i] == 0
                lemma_collect_step(a@, i as nat);
                assert(collect_nonzero_prefix(a@, (i as nat) + 1) == collect_nonzero_prefix(a@, i as nat));
                assert(indices@ == collect_nonzero_prefix(a@, (i as nat) + 1));
            }
        }
        i = i + 1;
    }
    proof {
        // At loop exit: i == n, indices@ == collect_nonzero_prefix(a@, n as nat)
        lemma_collect_properties(a@, n as nat);
    }
    indices
}
// </vc-code>

}
fn main() {}