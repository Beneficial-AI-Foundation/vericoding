// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed type conversions and ghost code usage */
spec fn all_same_from_index(s: Seq<char>, i: int) -> bool
    recommends i >= 0,
    ensures
        all_same_from_index(s, i) <==> (forall|j: int| i <= j < s.len() ==> #[trigger] s[j] == s[i]),
{
    if i >= s.len() {
        true
    } else {
        forall|j: int| i <= j < s.len() ==> s[j] == s[i]
    }
}

proof fn lemma_all_same_implies_same_as_first(s: Seq<char>, i: int)
    requires
        i >= 0,
        all_same_from_index(s, i),
        i < s.len(),
    ensures
        forall|j: int| i <= j < s.len() ==> s[j] == s[i],
{
}

proof fn lemma_not_all_same_implies_exists_different(s: Seq<char>)
    requires
        s.len() > 0,
        !all_same_from_index(s, 0),
    ensures
        exists|i: int| 0 <= i < s.len() && #[trigger] s[i] != s[0],
{
    if s.len() > 1 {
        proof {
            assert(!all_same_from_index(s, 0));
            assert(!(forall|j: int| 0 <= j < s.len() ==> s[j] == s[0]));
            assert(exists|j: int| 0 <= j < s.len() && s[j] != s[0]);
        }
    }
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
/* code modified by LLM (iteration 5): Fixed type conversion errors by using proper int comparisons */
{
    if s.len() == 0 {
        true
    } else {
        let mut i: int = 0;
        while i < s.len()
            invariant
                0 <= i <= s.len(),
                all_same_from_index(s, 0) <==> all_same_from_index(s, i),
        {
            if i > 0 && s[i as usize] != s[(i-1) as usize] {
                return false;
            }
            i = i + 1;
        }
        true
    }
}
// </vc-code>

}
fn main() {}