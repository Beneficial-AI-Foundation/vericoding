use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_seq_last_index_property<S>(s: Seq<S>, elem: S, i: int, j: int)
    requires
        0 <= i <= j < s.len(),
        s[j] == elem,
        forall|k: int| j < k < s.len() ==> s[k] != elem,
    ensures
        exists|k: int| i <= k <= j && s[k] == elem && forall|l: int| k < l <= j ==> s[l] != elem,
    decreases j - i,
{
    if s[i] == elem {
        assert(forall|l: int| i < l <= j ==> s[l] != elem) by {
            if exists|l: int| i < l <= j && s[l] == elem {
                let l = choose|l: int| i < l <= j && s[l] == elem();
                assert(s[l] == elem);
                assert(l <= j);
                assert(j < l < s.len() ==> s[l] != elem); // Contradiction
            }
        }
    } else {
        lemma_seq_last_index_property(s, elem, i + 1, j);
    }
}

proof fn lemma_exists_last_index<S>(s: Seq<S>, elem: S)
    requires
        exists|i: int| 0 <= i < s.len() && s[i] == elem,
    ensures
        exists|i: int| 0 <= i < s.len() && s[i] == elem && forall|j: int| i < j < s.len() ==> s[j] != elem,
{
    let i0 = choose|i: int| 0 <= i < s.len() && s[i] == elem();
    lemma_seq_last_index_property(s, elem, 0, i0);
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn last_position(a: &[i32], elem: i32) -> (result: usize)
    // pre-conditions-start
    requires
        0 < a.len() < 100_000,
        exists|i: int| 0 <= i < a.len() && a[i] == elem,
    // pre-conditions-end
    // post-conditions-start
    ensures
        0 <= result < a.len(),
        forall|i: int| result < i < a.len() ==> a[i] != elem,
        a[result as int] == elem,
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut idx: usize = (a.len() - 1) as usize;
    proof {
        lemma_exists_last_index(a@, elem);
    }
    while idx > 0
        invariant
            0 <= idx < a.len(),
            forall|i: int| idx < i < a.len() ==> a@[i] != elem,
        decreases idx,
    {
        if a[idx] == elem {
            break;
        }
        idx = idx - 1;
    }
    assert(a[idx] == elem) by {
        if idx == 0 {
            assert(a@[0] == elem);
        }
    };
    idx
}
// </vc-code>

fn main() {}
}