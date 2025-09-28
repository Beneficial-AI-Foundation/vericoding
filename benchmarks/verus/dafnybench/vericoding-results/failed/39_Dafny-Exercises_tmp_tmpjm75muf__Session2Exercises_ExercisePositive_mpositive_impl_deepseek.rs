use vstd::prelude::*;

verus! {

spec fn positive(s: Seq<int>) -> bool {
    forall|u: int| 0 <= u < s.len() ==> s[u] >= 0
}

// <vc-helpers>
spec fn positive(s: Seq<int>) -> bool {
    forall|u: int| 0 <= u < s.len() ==> s[u] >= 0
}

proof fn lemma_positive_empty() 
    ensures positive(Seq::empty())
{
    assert(positive(Seq::empty())) by {
        assert forall|u: int| 0 <= u < 0 implies (#[trigger] Seq::empty()@[u]) >= 0 {
            assert(!(0 <= u < 0));
        }
    };
}

proof fn lemma_positive_cons(head: int, tail: Seq<int>)
    requires
        head >= 0,
        positive(tail),
    ensures
        positive(Seq::new(tail.len() + 1, |i: int| if i == 0 { head } else { tail[i - 1] })),
{
    let s = Seq::new(tail.len() + 1, |i: int| if i == 0 { head } else { tail[i - 1] });
    assert forall|u: int| 0 <= u < s.len() implies s[u] >= 0 by {
        if u == 0 {
            assert(s[u] == head);
        } else {
            assert(s[u] == tail[u - 1]);
            assert(0 <= u - 1 < tail.len());
            assert(tail[u - 1] >= 0);
        }
    };
}

proof fn lemma_positive_index(s: Seq<int>, u: int)
    requires
        positive(s),
        0 <= u < s.len(),
    ensures
        s[u] >= 0,
{
}

proof fn lemma_positive_subseq(s: Seq<int>, start: int, end: int)
    requires
        positive(s),
        0 <= start <= end <= s.len(),
    ensures
        positive(s.subrange(start, end)),
{
    assert forall|u: int| 0 <= u < end - start implies s.subrange(start, end)@[u] >= 0 by {
        let idx = start + u;
        assert(0 <= idx < s.len());
        assert(s.subrange(start, end)@[u] == s[idx]);
    };
}
// </vc-helpers>

// <vc-spec>
fn mpositive(v: &[int]) -> (b: bool)
    ensures b == positive(v@)
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    let len = v.len();
    while i < len
        invariant
            0 <= i <= len,
            forall|u: int| 0 <= u < i ==> v@[u] >= 0,
    {
        if v[i] < 0 {
            proof {
                assert(!(v@[i] >= 0));
                assert(!positive(v@));
            }
            return false;
        }
        proof {
            assert(v@[i] >= 0);
            assert forall|u: int| 0 <= u < i + 1 implies v@[u] >= 0 by {
                if u < i {
                    assert(0 <= u < i);
                } else if u == i {
                    assert(v@[u] >= 0);
                }
            };
        }
        i = i + 1;
    }
    proof {
        assert(i == len);
        assert(forall|u: int| 0 <= u < len ==> v@[u] >= 0);
        assert(positive(v@));
    }
    true
}
// </vc-code>

fn main() {
}

}