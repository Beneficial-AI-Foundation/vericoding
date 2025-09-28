// <vc-preamble>
use vstd::prelude::*;
use vstd::multiset::Multiset;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed 'assert forall' syntax with 'by(arith)' */
proof fn lemma_partition_multiset(s: Multiset<int>, p: int)
    ensures
        s.filter(|z: int| z <= p).add(s.filter(|z: int| z > p)) == s,
{
    vstd::multiset::lemma_filter_splits(s, |z: int| z <= p);
    assert forall |z: int| !(z <= p) <==> z > p by(arith);
    vstd::multiset::lemma_filter_extensionality(s, |z: int| !(z <= p), |z: int| z > p);
}
// </vc-helpers>

// <vc-spec>
fn partition(Ghost(m): Ghost<Multiset<int>>) -> (res: (Ghost<Multiset<int>>, Ghost<int>, Ghost<Multiset<int>>))
    requires m.len() > 0
    ensures 
        ({
            let (Ghost(pre), Ghost(p), Ghost(post)) = res;
            &&& m.contains(p)
            &&& m == pre.add(Multiset::singleton(p)).add(post)
            &&& forall|z: int| pre.contains(z) ==> z <= p
            &&& forall|z: int| post.contains(z) ==> z >= p
        })
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Logic is sound; only the helper function needed a fix. */
    let p = m.choose();
    let m_rest = m.sub(Multiset::singleton(p));

    let pre = m_rest.filter(|z: int| z <= p);
    let post = m_rest.filter(|z: int| z > p);

    proof {
        lemma_partition_multiset(m_rest, p);
    }

    (Ghost(pre), Ghost(p), Ghost(post))
}
// </vc-code>

}
fn main() {}