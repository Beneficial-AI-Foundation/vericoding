use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_bound_index_for_seq_new(k: int, n: int)
    requires
        0 <= k,
        k < 2 * n,
        k % 2 != 0,
    ensures
        0 <= (k - 1) / 2 < n,
{
    assert(k != 0);
    assert(0 < k);
    assert(k >= 1);
    assert(k <= 2 * n - 1);
    assert(k - 1 <= 2 * n - 2);
    assert(0 <= k - 1);
    assert(0 <= (k - 1) / 2);
    assert((k - 1) / 2 <= (2 * n - 2) / 2);
    assert((2 * n - 2) / 2 == n - 1);
    assert((k - 1) / 2 <= n - 1);
    assert((k - 1) / 2 < n);
}
// </vc-helpers>

// <vc-spec>
#[verifier::exec_allows_no_decreases_clause]
fn insert_before_each(s: Seq<String>, x: String) -> (v: Seq<String>)
    ensures
        v.len() == 2 * s.len(),
        forall|i: int| 0 <= i < s.len() ==> v[2*i] == x && v[2*i + 1] == s[i],
// </vc-spec>
// <vc-code>
{
    let n = s.len();
    let v = Seq::new(n + n, |k: int|
        if k % 2 == 0 {
            x.clone()
        } else {
            proof {
                // Within Seq::new, we have 0 <= k < n + n, i.e., k < 2 * n
                lemma_bound_index_for_seq_new(k, n);
            }
            let i = (k - 1) / 2;
            s.index(i)
        }
    );
    v
}
// </vc-code>

fn main() {}

}