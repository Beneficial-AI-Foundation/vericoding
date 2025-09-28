// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn starts_with(s: Seq<char>, p: Seq<char>) -> bool
    decreases s.len() + p.len()
{
    p.len() == 0 || (s.len() != 0 && s.len() >= p.len() && s[0] == p[0] && starts_with(s.subrange(1, s.len() as int), p.subrange(1, p.len() as int)))
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): prefix lemma using elementwise equality to derive starts_with */
proof fn lemma_prefix_eq_implies_starts_with(s: Seq<char>, p: Seq<char>)
    requires
        s.len() >= p.len(),
        forall|j: int| 0 <= j < p.len() ==> s[j] == p[j],
    ensures
        starts_with(s, p),
    decreases p.len()
{
    if p.len() == 0 {
        assert(starts_with(s, p));
    } else {
        assert(s.len() != 0);
        assert(s[0] == p[0]) by {
            assert(0 < p.len());
        };
        let s1 = s.subrange(1, s.len() as int);
        let p1 = p.subrange(1, p.len() as int);
        assert(s1.len() == s.len() - 1);
        assert(p1.len() == p.len() - 1);
        assert(s1.len() >= p1.len()) by {
            assert(s.len() >= p.len());
        };
        assert(forall|j: int| 0 <= j < p1.len() ==> s1[j] == p1[j]) by {
            assert(s1.len() == s.len() - 1);
            assert(p1.len() == p.len() - 1);
            assert forall|j: int| 0 <= j && j < p1.len() implies s1[j] == p1[j] by {
                assert(0 <= j + 1);
                assert(j + 1 < p.len());
                assert(j + 1 <= s.len());
                assert(j < s1.len());
                assert(s1[j] == s[j + 1]);
                assert(p1[j] == p[j + 1]);
                assert(s[j + 1] == p[j + 1]);
            };
        };
        lemma_prefix_eq_implies_starts_with(s1, p1);
        assert(starts_with(s, p));
    }
}

/* helper modified by LLM (iteration 4): loop-based executable prefix check implying starts_with when true */
fn has_prefix(v: &Vec<char>, p: &Vec<char>) -> (b: bool)
    ensures
        b ==> starts_with(v@, p@),
{
    let mut i: usize = 0;
    while i < p.len()
        invariant
            0 <= i as int <= p@.len(),
            i as int <= v@.len(),
            forall|j: int| 0 <= j < i as int ==> v@[j] == p@[j],
        decreases p@.len() - i as int
    {
        if i >= v.len() {
            return false;
        }
        let vc = v[i];
        let pc = p[i];
        if vc != pc {
            return false;
        }
        i = i + 1;
    }
    proof {
        assert(i as int == p@.len());
        assert(v@.len() >= p@.len());
        assert(forall|j: int| 0 <= j < p@.len() ==> v@[j] == p@[j]) by {
            assert forall|j: int| 0 <= j && j < p@.len() implies v@[j] == p@[j] by {
                assert(j < i as int);
            };
        };
        lemma_prefix_eq_implies_starts_with(v@, p@);
    }
    true
}
// </vc-helpers>

// <vc-spec>
fn filter_by_prefix(xs: Vec<Vec<char>>, p: Vec<char>) -> (filtered: Vec<Vec<char>>)
    ensures forall|i: int| 0 <= i < filtered@.len() ==> starts_with(#[trigger] filtered@[i]@, #[trigger] p@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): build filtered list while maintaining invariant; avoid calling clone in proof context */
    let mut filtered: Vec<Vec<char>> = Vec::new();
    let mut i: usize = 0;
    while i < xs.len()
        invariant
            0 <= i as int <= xs@.len(),
            filtered@.len() <= i as int,
            forall|k: int| 0 <= k < filtered@.len() ==> starts_with(#[trigger] filtered@[k]@, #[trigger] p@),
        decreases xs@.len() - i as int
    {
        let v_keep = xs[i].clone();
        let b = has_prefix(&v_keep, &p);
        i = i + 1;
        if b {
            // Prepare element to push and relate its spec-view to v_keep@
            let to_push = v_keep.clone();
            proof {
                // From has_prefix's ensures and b, we know v_keep has the prefix
                assert(starts_with(v_keep@, p@));
                // From clone's spec, to_push@ == v_keep@
                assert(to_push@ == v_keep@);
            }
            let ghost filtered_old = filtered@;
            filtered.push(to_push);
            proof {
                // Vec push postcondition gives this exact relation
                assert(filtered@ == filtered_old.push(to_push));
                let old_len = filtered_old.len();
                assert(filtered@.len() == old_len + 1);
                assert(forall|k: int| 0 <= k < filtered@.len() ==> starts_with(#[trigger] filtered@[k]@, #[trigger] p@)) by {
                    assert forall|k: int| 0 <= k && k < filtered@.len() implies starts_with(filtered@[k]@, p@) by {
                        if k < old_len {
                            assert(filtered@[k] == filtered_old[k]);
                            assert(starts_with(filtered_old[k]@, p@));
                            assert(starts_with(filtered@[k]@, p@));
                        } else {
                            assert(k == old_len);
                            assert(filtered@[k] == to_push);
                            // Using earlier facts: to_push@ == v_keep@ and starts_with(v_keep@, p@)
                            assert(starts_with(to_push@, p@));
                        }
                    };
                };
            }
        }
    }
    filtered
}
// </vc-code>


}

fn main() {}