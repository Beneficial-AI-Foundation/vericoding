// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_prefixes(s: Seq<char>, result: Seq<Seq<char>>) -> bool {
    result.len() == s.len() &&
    forall|i: int| 0 <= i < result.len() ==> result[i] == s.subrange(0, i + 1)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): corrected forall-assert syntax and added extensionality to equate sequences after push */
proof fn lemma_subrange_push<T>(s: Seq<T>, j: int)
    requires
        0 <= j < s.len(),
    ensures
        s.subrange(0, j).push(s[j]) == s.subrange(0, j + 1),
{
    let left = s.subrange(0, j).push(s[j]);
    let right = s.subrange(0, j + 1);
    assert(s.subrange(0, j).len() == j);
    assert(left.len() == j + 1);
    assert(right.len() == j + 1);
    assert forall |i: int| 0 <= i < left.len() implies left[i] == right[i] by {
        if i < j {
            assert(i < s.subrange(0, j).len());
            assert(left[i] == s.subrange(0, j)[i]);
            assert(s.subrange(0, j)[i] == s[i]);
            assert(right[i] == s[i]);
        } else {
            assert(i == j);
            assert(left[i] == s[j]);
            assert(right[i] == s[i]);
        }
    }
    assert(left == right);
}
// </vc-helpers>

// <vc-spec>
fn all_prefixes(s: Vec<char>) -> (result: Vec<Vec<char>>)
    ensures valid_prefixes(s@, result@.map(|i, v: Vec<char>| v@))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): parenthesized s@ usages to fix parsing, and simplified proofs while maintaining invariants */
    let mut result: Vec<Vec<char>> = Vec::new();
    let mut prefix: Vec<char> = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i as int <= s.len() as int,
            (result@).len() == i as int,
            (result@).len() <= (s@).len(),
            forall|k: int| 0 <= k < (result@).len() ==> (result@[k])@ == (s@).subrange(0, k + 1),
            prefix@ == (s@).subrange(0, i as int),
        decreases (s.len() - i) as int
    {
        let ch = s[i];
        let ghost old_prefix = prefix@;
        proof {
            assert((s@).len() == s.len() as int);
            assert(i < s.len());
            lemma_subrange_push::<char>(s@, i as int);
            assert(ch == s@[i as int]);
        }
        prefix.push(ch);
        proof {
            assert(prefix@ == old_prefix.push(ch));
            assert(old_prefix == (s@).subrange(0, i as int));
            assert(old_prefix.push(s@[i as int]) == (s@).subrange(0, (i as int) + 1));
            assert(prefix@ == (s@).subrange(0, (i as int) + 1));
        }
        let snapshot = prefix.clone();
        result.push(snapshot);
        i += 1;
    }
    proof {
        assert((s@).len() == s.len() as int);
    }
    assert((result@).len() == (s@).len());
    result
}
// </vc-code>


}

fn main() {}