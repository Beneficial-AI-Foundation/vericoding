// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): refined subrange push lemma with explicit index reasoning */
proof fn lemma_subrange_push_last<T>(s: Seq<T>, i: int)
    requires
        0 <= i,
        i < s.len() as int,
    ensures
        s.subrange(0, i).push(s[i]) == s.subrange(0, i + 1),
{
    assert forall|k: int|
        0 <= k < i + 1 implies #[trigger] (s.subrange(0, i).push(s[i]))[k] == s.subrange(0, i + 1)[k] by {
        if k < i {
            assert(0 <= k < i);
            assert((s.subrange(0, i).push(s[i]))[k] == s.subrange(0, i)[k]);
            assert(s.subrange(0, i)[k] == s[k]);
            assert(s.subrange(0, i + 1)[k] == s[k]);
        } else {
            assert(k == i);
            assert((s.subrange(0, i).push(s[i]))[k] == s[i]);
            assert(s.subrange(0, i + 1)[k] == s[k]);
        }
    }
}

/* helper modified by LLM (iteration 3): clarified full-range subrange equality proof */
proof fn lemma_subrange_full<T>(s: Seq<T>)
    ensures
        s.subrange(0, s.len() as int) == s,
{
    assert(s.subrange(0, s.len() as int).len() == s.len());
    assert forall|k: int| 0 <= k < s.len() as int implies #[trigger] s.subrange(0, s.len() as int)[k] == s[k] by { }
}
// </vc-helpers>

// <vc-spec>
fn copy<T: Copy>(a: &Vec<T>) -> (result: Vec<T>)
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == a[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): strengthened loop invariants and bounds reasoning for subrange and indexing */
    let len = a.len();
    let ghost s = a@;
    let mut result: Vec<T> = Vec::new();
    let mut i: usize = 0;
    while i < len
        invariant
            a@ == s,
            len == a.len(),
            i <= len,
            0 <= i as int,
            (i as int) <= s.len() as int,
            result.len() == i,
            result@ == s.subrange(0, i as int),
        decreases (len - i) as int
    {
        // Safe to index into a because i < len and len == a.len()
        let v = a[i];
        proof {
            // relate concrete value to the sequence view
            assert(v == a@[i as int]);
            assert(a@ == s);
            assert(v == s[i as int]);
        }
        result.push(v);
        proof {
            // show preconditions for the subrange push lemma
            assert(0 <= i as int);
            assert(i < len);
            assert(len == a.len());
            assert(s.len() as int == a.len() as int);
            assert((i as int) < s.len() as int);
            lemma_subrange_push_last::<T>(s, i as int);
        }
        i = i + 1;
    }
    proof {
        assert(i == len);
        assert(len == a.len());
        assert(s.len() as int == a.len() as int);
        assert(i as int == s.len() as int);
        lemma_subrange_full::<T>(s);
    }
    result
}
// </vc-code>

}
fn main() {}