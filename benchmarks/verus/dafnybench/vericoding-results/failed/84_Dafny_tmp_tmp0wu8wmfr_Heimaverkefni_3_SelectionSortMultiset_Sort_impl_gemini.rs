// <vc-preamble>
use vstd::prelude::*;
use vstd::multiset::*;

verus! {

proof fn min_of_multiset(m: Multiset<int>) -> (min: int)
    requires 
        m.len() > 0,
    ensures 
        m.count(min) > 0,
        forall|z: int| m.count(z) > 0 ==> min <= z,
{
    assume(false);
    arbitrary()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed the proof within sort_rec */
spec fn is_sorted(s: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
}

proof fn sort_rec(m: Multiset<int>) -> (s: Seq<int>)
    ensures
        s.to_multiset() == m,
        is_sorted(s),
    decreases m.len(),
{
    if m.len() == 0 {
        Seq::empty()
    } else {
        let min = min_of_multiset(m);
        assert(m.count(min) > 0);

        let m_rest = m.remove(min);
        let s_rest = sort_rec(m_rest);
        let s = seq![min].add(s_rest);

        lemma_remove_add(m, min);
        assert(m_rest.add(min) == m);
        assert(s.to_multiset() == seq![min].to_multiset().union(s_rest.to_multiset()));
        assert(s.to_multiset() == Multiset::singleton(min).union(m_rest));
        assert(Multiset::singleton(min).union(m_rest) == m_rest.add(min));

        proof {
            assert(is_sorted(s_rest));
            
            assert forall |y: int| s_rest.contains(y) implies min <= y by {
                assert(s_rest.to_multiset().count(y) > 0);
                assert(m_rest.count(y) > 0);
                assert(m.remove(min).le(m));
                assert(m.count(y) > 0);
                assert(forall|z: int| m.count(z) > 0 ==> min <= z);
                assert(min <= y);
            }

            assert forall |i: int, j: int| 0 <= i < j < s.len() implies s[i] <= s[j] by {
                if i == 0 {
                    let y = s[j];
                    assert(s_rest.contains(y));
                    assert(min <= y);
                    assert(s[i] <= s[j]);
                } else {
                    assert(is_sorted(s_rest));
                    assert(s_rest[i - 1] <= s_rest[j - 1]);
                    assert(s[i] <= s[j]);
                }
            }
            assert(is_sorted(s));
        }
        s
    }
}
// </vc-helpers>

// <vc-spec>
exec fn sort(m: Multiset<int>) -> (s: Vec<int>)

    ensures 
        s@.to_multiset() == m,
        forall|p: int, q: int| 0 <= p < q < s.len() ==> s[p] <= s[q],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): correctly build the Vec from the ghost Seq */
{
    let s_spec = sort_rec(m);
    let mut s: Vec<int> = Vec::new();
    let mut i: usize = 0;
    while i < s_spec.len()
        invariant
            i <= s_spec.len(),
            s.len() == i,
            s@ == s_spec.subrange(0, i as int),
        decreases s_spec.len() - i
    {
        s.push(s_spec[i as int]);
        i = i + 1;
    }

    assert(s@ == s_spec) by {
        assert(s.len() == s_spec.len());
        assert(s@ == s_spec.subrange(0, s_spec.len() as int));
    }
    
    assert(s_spec.to_multiset() == m);
    assert(is_sorted(s_spec));

    assert(s@.to_multiset() == m);
    assert(is_sorted(s@));

    s
}
// </vc-code>

}
fn main() {}