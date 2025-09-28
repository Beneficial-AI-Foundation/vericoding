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
/* helper modified by LLM (iteration 3): [no functional changes to helper] */
proof fn lemma_is_sorted_push(s: Seq<i32>, x: i32)
    requires
        is_sorted(s),
        s.len() > 0 ==> s.last() <= x,
    ensures
        is_sorted(s.push(x)),
{
    let s_new = s.push(x);
    assert forall|i: int, j: int| 0 <= i < j < s_new.len() implies s_new[i] <= s_new[j] by {
        if j < s.len() {
            // Case 1: i and j are both indices into the original sequence s.
            // s_new[i] == s[i] and s_new[j] == s[j].
            // The property holds because s is sorted.
            assert(s[i] <= s[j]);
        } else {
            // Case 2: j is the index of the new element x.
            assert(j == s.len());
            assert(i < s.len());
            if s.len() > 0 {
                // We know s is sorted, so s[i] <= s.last().
                assert(s[i] <= s.last());
                // From the requires clause, we know s.last() <= x.
                assert(s.last() <= x);
                // Therefore, s[i] <= x.
                assert(s[i] <= x);
            }
            // If s.len() == 0, then i < s.len() is false, so this path is unreachable.
        }
    }
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
    /* code modified by LLM (iteration 3): [fixed compilation error by using spec indexing `@` operator in proof blocks] */
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    let mut j: usize = 0;

    let a_len = a.len();
    let b_len = b.len();

    while i < a_len && j < b_len
        invariant
            a@.len() == a_len as int,
            b@.len() == b_len as int,
            0 <= i <= a_len,
            0 <= j <= b_len,
            is_sorted(result@),
            multiset_equiv(a@ + b@, result@ + a@.subrange(i as int, a_len as int) + b@.subrange(j as int, b_len as int)),
            result@.len() > 0 ==> (i < a_len ==> result@.last() <= a@[i as int]),
            result@.len() > 0 ==> (j < b_len ==> result@.last() <= b@[j as int]),
        decreases (a_len - i) + (b_len - j)
    {
        let current_a = a[i];
        let current_b = b[j];
        if current_a <= current_b {
            proof {
                assert(a@.subrange(i as int, a_len as int) === seq![a@[i as int]] + a@.subrange((i + 1) as int, a_len as int));
                lemma_is_sorted_push(result@, current_a);
            }
            result.push(current_a);
            i = i + 1;
        } else {
            proof {
                assert(b@.subrange(j as int, b_len as int) === seq![b@[j as int]] + b@.subrange((j + 1) as int, b_len as int));
                lemma_is_sorted_push(result@, current_b);
            }
            result.push(current_b);
            j = j + 1;
        }
    }

    while i < a_len
        invariant
            a@.len() == a_len as int,
            b@.len() == b_len as int,
            0 <= i <= a_len,
            j == b_len,
            is_sorted(result@),
            multiset_equiv(a@ + b@, result@ + a@.subrange(i as int, a_len as int) + b@.subrange(j as int, b_len as int)),
            result@.len() > 0 ==> (i < a_len ==> result@.last() <= a@[i as int]),
        decreases a_len - i
    {
        let current_a = a[i];
        proof {
            assert(a@.subrange(i as int, a_len as int) === seq![a@[i as int]] + a@.subrange((i + 1) as int, a_len as int));
            assert(b@.subrange(j as int, b_len as int).len() == 0);
            lemma_is_sorted_push(result@, current_a);
        }
        result.push(current_a);
        i = i + 1;
    }

    while j < b_len
        invariant
            a@.len() == a_len as int,
            b@.len() == b_len as int,
            i == a_len,
            0 <= j <= b_len,
            is_sorted(result@),
            multiset_equiv(a@ + b@, result@ + a@.subrange(i as int, a_len as int) + b@.subrange(j as int, b_len as int)),
            result@.len() > 0 ==> (j < b_len ==> result@.last() <= b@[j as int]),
        decreases b_len - j
    {
        let current_b = b[j];
        proof {
            assert(b@.subrange(j as int, b_len as int) === seq![b@[j as int]] + b@.subrange((j + 1) as int, b_len as int));
            assert(a@.subrange(i as int, a_len as int).len() == 0);
            lemma_is_sorted_push(result@, current_b);
        }
        result.push(current_b);
        j = j + 1;
    }

    result
}
// </vc-code>

}
fn main() {}