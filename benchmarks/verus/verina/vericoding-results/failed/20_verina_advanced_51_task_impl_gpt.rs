// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_sorted(s: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
}

spec fn multiset_equiv(s1: Seq<i32>, s2: Seq<i32>) -> bool {
    s1.to_multiset() == s2.to_multiset()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): fix nat/int casts and complete proofs */
proof fn lemma_sorted_push_extends(s: Seq<i32>, x: i32)
    requires
        is_sorted(s),
        s.len() == 0 || (0 < s.len() && s[(s.len() as int) - 1] <= x)
    ensures
        is_sorted(s.push(x))
{
    let n: int = s.len() as int;
    assert forall |i: int, j: int| 0 <= i < j < n + 1 implies s.push(x)[i] <= s.push(x)[j] by {
        if j < n {
            assert(s.push(x)[i] == s[i]);
            assert(s.push(x)[j] == s[j]);
            assert(is_sorted(s));
            // from is_sorted(s): 0 <= i < j < s.len()
        } else {
            assert(j == n);
            assert(0 <= i < n);
            assert(s.push(x)[i] == s[i]);
            assert(s.push(x)[n] == x);
            if n == 0 {
                // impossible since 0 <= i < 0
            } else {
                // n > 0; from precondition we have s[n-1] <= x
                assert(n > 0);
                assert(s[(s.len() as int) - 1] <= x);
                assert(s[n - 1] <= x);
                if i < n - 1 {
                    // is_sorted(s) gives s[i] <= s[n-1]
                    assert(is_sorted(s));
                    // Hence s[i] <= x by transitivity
                } else {
                    assert(i == n - 1);
                    // directly s[i] <= x
                }
            }
        }
    };
}

/* helper modified by LLM (iteration 2): add proper casts in prefix/push lemma */
proof fn lemma_prefix_push(s: Seq<i32>, k: int)
    requires
        0 <= k < s.len() as int
    ensures
        s.subrange(0, k + 1) == s.subrange(0, k).push(s[k])
{
    assert(s.subrange(0, k + 1).len() == s.subrange(0, k).push(s[k]).len());
    assert forall |i: int| 0 <= i < s.subrange(0, k + 1).len() as int implies s.subrange(0, k + 1)[i] == s.subrange(0, k).push(s[k])[i] by {
        if i < k {
            assert(s.subrange(0, k + 1)[i] == s[i]);
            assert(s.subrange(0, k)[i] == s[i]);
            assert(s.subrange(0, k).push(s[k])[i] == s.subrange(0, k)[i]);
        } else {
            assert(i == k);
            assert(s.subrange(0, k + 1)[i] == s[i]);
            assert(s.subrange(0, k).push(s[k])[i] == s[k]);
        }
    };
}

// </vc-helpers>

// <vc-spec>
fn merge_sorted(a: Vec<i32>, b: Vec<i32>) -> (result: Vec<i32>)
    requires 
        is_sorted(a@),
        is_sorted(b@),
    ensures 
        is_sorted(result@),
        multiset_equiv(result@, a@ + b@),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): implement merge with proper nat/int casts and helper lemmas */
    let mut result: Vec<i32> = Vec::new();
    let mut ia: usize = 0;
    let mut ib: usize = 0;

    while ia < a.len() && ib < b.len()
        invariant
            is_sorted(result@),
            (result@.len() as int) == (ia as int) + (ib as int),
            result@.to_multiset() == (a@.subrange(0, ia as int) + b@.subrange(0, ib as int)).to_multiset(),
            0 <= ia as int <= a@.len() as int,
            0 <= ib as int <= b@.len() as int,
            ((result@.len() as int) == 0) || (
                (ia < a.len() ==> result@[(result@.len() as int) - 1] <= a@[ia as int]) &&
                (ib < b.len() ==> result@[(result@.len() as int) - 1] <= b@[ib as int])
            ),
        decreases ((a@.len() as int) - ia as int) + ((b@.len() as int) - ib as int)
    {
        let va = a[ia];
        let vb = b[ib];
        if va <= vb {
            proof { lemma_sorted_push_extends(result@, va); }
            let pre_ia = ia;
            result.push(va);
            ia = ia + 1;
            proof {
                lemma_prefix_push(a@, pre_ia as int);
            }
        } else {
            proof { lemma_sorted_push_extends(result@, vb); }
            let pre_ib = ib;
            result.push(vb);
            ib = ib + 1;
            proof {
                lemma_prefix_push(b@, pre_ib as int);
            }
        }
    }

    while ia < a.len()
        invariant
            is_sorted(result@),
            (result@.len() as int) == (ia as int) + (ib as int),
            result@.to_multiset() == (a@.subrange(0, ia as int) + b@.subrange(0, ib as int)).to_multiset(),
            0 <= ia as int <= a@.len() as int,
            0 <= ib as int <= b@.len() as int,
            ((result@.len() as int) == 0) || (ia < a.len() ==> result@[(result@.len() as int) - 1] <= a@[ia as int]),
        decreases (a@.len() as int) - ia as int
    {
        let va = a[ia];
        proof { lemma_sorted_push_extends(result@, va); }
        let pre_ia = ia;
        result.push(va);
        ia = ia + 1;
        proof { lemma_prefix_push(a@, pre_ia as int); }
    }

    while ib < b.len()
        invariant
            is_sorted(result@),
            (result@.len() as int) == (ia as int) + (ib as int),
            result@.to_multiset() == (a@.subrange(0, ia as int) + b@.subrange(0, ib as int)).to_multiset(),
            0 <= ia as int <= a@.len() as int,
            0 <= ib as int <= b@.len() as int,
            ((result@.len() as int) == 0) || (ib < b.len() ==> result@[(result@.len() as int) - 1] <= b@[ib as int]),
        decreases (b@.len() as int) - ib as int
    {
        let vb = b[ib];
        proof { lemma_sorted_push_extends(result@, vb); }
        let pre_ib = ib;
        result.push(vb);
        ib = ib + 1;
        proof { lemma_prefix_push(b@, pre_ib as int); }
    }

    proof {
        assert(a@.subrange(0, a@.len() as int) == a@);
        assert(b@.subrange(0, b@.len() as int) == b@);
    }

    result
}
// </vc-code>

}
fn main() {}