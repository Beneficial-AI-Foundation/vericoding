use vstd::prelude::*;

verus! {

spec fn positive(s: Seq<int>) -> bool {
    forall|u: int| 0 <= u < s.len() ==> s[u] >= 0
}

// <vc-helpers>
proof fn lemma_forall_range_push_one_nonneg(s: Seq<int>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        ((forall|u: int| 0 <= u < i ==> #[trigger] s[u] >= 0) && s[i] >= 0)
            == (forall|u: int| 0 <= u < i + 1 ==> #[trigger] s[u] >= 0)
{
    // Direction: ((forall u < i) && s[i]) ==> (forall u < i+1)
    assert(((forall|u: int| 0 <= u < i ==> #[trigger] s[u] >= 0) && s[i] >= 0)
        ==> (forall|u: int| 0 <= u < i + 1 ==> #[trigger] s[u] >= 0)) by {
        assert forall|u: int| 0 <= u < i + 1 implies s[u] >= 0 by {
            if u < i {
                // Use the first conjunct
                assert(0 <= u < i);
            } else {
                // Here u >= i and u < i + 1, hence u == i
                assert(u >= i);
                assert(u <= i); // from u < i + 1
                assert(u == i);
            }
        }
    };

    // Direction: (forall u < i+1) ==> ((forall u < i) && s[i])
    assert((forall|u: int| 0 <= u < i + 1 ==> #[trigger] s[u] >= 0)
        ==> ((forall|u: int| 0 <= u < i ==> #[trigger] s[u] >= 0) && s[i] >= 0)) by {
        // Prove forall u < i
        assert(forall|u: int| 0 <= u < i ==> #[trigger] s[u] >= 0) by {
            assert forall|u: int| 0 <= u < i implies s[u] >= 0 by {
                assert(0 <= u < i + 1);
            }
        }
        // Prove s[i] >= 0 using i < i+1
        assert(0 <= i);
        assert(i < i + 1);
    };
}
// </vc-helpers>

// <vc-spec>
fn mpositive(v: &[int]) -> (b: bool)
    ensures b == positive(v@)
// </vc-spec>
// <vc-code>
{
    let mut res: bool = true;
    let mut i: usize = 0;
    while i < v.len()
        invariant i <= v.len()
        invariant res == (forall|u: int| 0 <= u < i as int ==> #[trigger] v@[u] >= 0)
    {
        assert(v@.len() == v.len() as int);
        assert(i as int < v@.len());
        assert(v@[i as int] == v[i]);

        let
// </vc-code>

fn main() {
}

}