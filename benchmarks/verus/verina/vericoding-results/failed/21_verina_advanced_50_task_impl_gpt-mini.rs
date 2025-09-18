// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_sorted(v: Seq<nat>) -> bool {
    forall|i: int, j: int| 0 <= i < j < v.len() ==> #[trigger] v[i] <= #[trigger] v[j]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): concat index of appended single element */
proof fn concat_index_single(s: Seq<nat>, x: nat, k: int)
    requires
        0 <= k && k < s.len() + 1,
    ensures
        (s + seq![x])@[k] == if k < s.len() { s@[k] } else { x },
{
    proof {
        if k < s.len() {
            // index falls in original sequence
            assert (s + seq![x])@[k] == s@[k];
        } else {
            // index is the appended element
            assert (s + seq![x])@[k] == x;
        }
    }
}

/* helper modified by LLM (iteration 5): append element preserves sortedness */
proof fn append_preserves_sorted(s: Seq<nat>, x: nat)
    requires
        is_sorted(s),
        s.len() == 0 || s@[s.len() - 1] <= x,
    ensures
        is_sorted(s + seq![x]),
{
    proof {
        assert forall|i: int, j: int| 0 <= i < j < s.len() + 1 ==>
            (s + seq![x])@[i] <= (s + seq![x])@[j] by {
                if j < s.len() {
                    // both indices refer to original sequence
                    assert (s + seq![x])@[i] == s@[i];
                    assert (s + seq![x])@[j] == s@[j];
                    assert s@[i] <= s@[j];
                } else {
                    // j == s.len() refers to appended element
                    assert (s + seq![x])@[j] == x;
                    assert (s + seq![x])@[i] == s@[i];
                    // from 0 <= i < j == s.len() we get s.len() > 0
                    assert s.len() > 0;
                    assert s@[i] <= s@[s.len() - 1];
                    assert s@[s.len() - 1] <= x;
                    assert s@[i] <= x;
                }
            };
    }
}

/* helper modified by LLM (iteration 5): sequence slice push equality */
proof fn seq_slice_push(s: Seq<nat>, i: int)
    requires
        0 <= i && i < s.len(),
    ensures
        s.slice(0, i + 1) == s.slice(0, i) + seq![s@[i]],
{
    proof {
        assert forall|k: int| 0 <= k < i + 1 ==>
            s.slice(0, i + 1)@[k] == (s.slice(0, i) + seq![s@[i]])@[k] by {
                if k < i {
                    assert s.slice(0, i + 1)@[k] == s@[k];
                    assert (s.slice(0, i) + seq![s@[i]])@[k] == s@[k];
                } else {
                    assert s.slice(0, i + 1)@[k] == s@[i];
                    assert (s.slice(0, i) + seq![s@[i]])@[k] == s@[i];
                }
            };
    }
}

/* helper modified by LLM (iteration 5): multiset of append with single element */
proof fn multiset_append_single(s: Seq<nat>, x: nat)
    ensures
        (s + seq![x]).to_multiset() == s.to_multiset().add(seq![x].to_multiset()),
{
    proof {
        assert forall|v: nat| ((s + seq![x]).to_multiset().count(v) == s.to_multiset().count(v) + seq![x].to_multiset().count(v)) by {
            if v == x {
                assert (s + seq![x]).to_multiset().count(v) == s.to_multiset().count(v) + 1;
            } else {
                assert (s + seq![x]).to_multiset().count(v) == s.to_multiset().count(v) + 0;
            }
        };
        assert (s + seq![x]).to_multiset() == s.to_multiset().add(seq![x].to_multiset());
    }
}

/* helper modified by LLM (iteration 5): prefix of sorted sequence is sorted */
proof fn prefix_sorted(s: Seq<nat>, n: int)
    requires
        is_sorted(s),
        0 <= n && n <= s.len(),
    ensures
        is_sorted(s.slice(0, n)),
{
    proof {
        assert forall|i: int, j: int| 0 <= i < j < n ==>
            s.slice(0, n)@[i] <= s.slice(0, n)@[j] by {
                assert s@[i] <= s@[j];
            };
    }
}

// </vc-helpers>

// <vc-spec>
fn merge_sorted(a1: &Vec<nat>, a2: &Vec<nat>) -> (result: Vec<nat>)
    requires 
        is_sorted(a1@),
        is_sorted(a2@),
    ensures
        is_sorted(result@),
        result@.to_multiset() == a1@.to_multiset().add(a2@.to_multiset()),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): merge two sorted vectors into one sorted vector */
    let mut result: Vec<nat> = Vec::new();
    let mut i: int = 0;
    let mut j: int = 0;
    let la: int = a1@.len();
    let lb: int = a2@.len();

    while i < la && j < lb
        invariant
            0 <= i <= la,
            0 <= j <= lb,
            result@.to_multiset() == a1@.slice(0, i).to_multiset().add(a2@.slice(0, j).to_multiset()),
            is_sorted(result@),
            (result@.len() == 0) || (forall|k: int| i <= k < la ==> result@[result@.len() - 1] <= a1@[k]),
            (result@.len() == 0) || (forall|k: int| j <= k < lb ==> result@[result@.len() - 1] <= a2@[k]),
        decreases
            la - i + lb - j
    {
        if a1@[i] <= a2@[j] {
            let prev: Seq<nat> = result@;
            let x: nat = a1@[i];
            result.push(x);
            proof {
                multiset_append_single(prev, x);
                seq_slice_push(a1@, i);
                append_preserves_sorted(prev, x);
            }
            i = i + 1;
        } else {
            let prev: Seq<nat> = result@;
            let x: nat = a2@[j];
            result.push(x);
            proof {
                multiset_append_single(prev, x);
                seq_slice_push(a2@, j);
                append_preserves_sorted(prev, x);
            }
            j = j + 1;
        }
    }

    while i < la
        invariant
            0 <= i <= la,
            result@.to_multiset() == a1@.slice(0, i).to_multiset().add(a2@.slice(0, j).to_multiset()),
            is_sorted(result@),
        decreases
            la - i
    {
        let prev: Seq<nat> = result@;
        let x: nat = a1@[i];
        result.push(x);
        proof {
            multiset_append_single(prev, x);
            seq_slice_push(a1@, i);
            append_preserves_sorted(prev, x);
        }
        i = i + 1;
    }

    while j < lb
        invariant
            0 <= j <= lb,
            result@.to_multiset() == a1@.slice(0, i).to_multiset().add(a2@.slice(0, j).to_multiset()),
            is_sorted(result@),
        decreases
            lb - j
    {
        let prev: Seq<nat> = result@;
        let x: nat = a2@[j];
        result.push(x);
        proof {
            multiset_append_single(prev, x);
            seq_slice_push(a2@, j);
            append_preserves_sorted(prev, x);
        }
        j = j + 1;
    }

    result
}

// </vc-code>

}
fn main() {}