// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): prove that if first n characters equal `first`, then they are pairwise equal */
proof fn all_equal_implies_pairwise(s: Seq<char>, n: int, first: char)
    requires
        0 <= n && n <= s.len() as int,
        forall|k: int| 0 <= k && k < n ==> s[k] == first,
    ensures
        forall|i: int, j: int| 0 <= i && i < n && 0 <= j && j < n ==> s[i] == s[j],
{
    forall|i: int, j: int| {
        if 0 <= i && i < n && 0 <= j && j < n {
            assert(s[i] == first);
            assert(s[j] == first);
            assert(s[i] == s[j]);
        }
    };
}

// </vc-helpers>

// <vc-spec>
fn all_characters_same(s: Seq<char>) -> (result: bool)
    requires true,
    ensures
        result ==> (forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() ==> s[i] == s[j]),
        !result ==> (s.len() > 0 && exists|i: int| 0 <= i < s.len() && #[trigger] s[i] != s[0]),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): compute result via spec quantifier using s[i] indexing and int conversion of len */
{
    let n: int = s.len() as int;
    if n == 0 {
        true
    } else {
        (forall|i: int, j: int| 0 <= i && i < n && 0 <= j && j < n ==> s[i] == s[j])
    }
}

// </vc-code>

}
fn main() {}