// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): used correct sequence indexing with @ and simplified spec */
proof fn lemma_all_same_from_first(s: Seq<u8>)
    requires
        s.len() > 0,
        forall|i: int| 0 <= i < s.len() ==> s@[i] == s@[0],
    ensures
        forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() ==> s@[i] == s@[j],
{
}
// </vc-helpers>

// <vc-spec>
fn all_characters_same(s: Seq<u8>) -> (result: bool)
    ensures
        result ==> (forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() ==> s[i] == s[j]),
        !result ==> (s.len() > 1) && (exists|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && i != j && s[i] != s[j])
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed all compilation errors (types, literals, sequence indexing) */
{
    if s.len() <= 1 {
        return true;
    }

    let mut i: usize = 1;
    while i < s.len()
        invariant
            s.len() > 1,
            1 <= i <= s.len(),
            forall|j: int| 0 <= j < i ==> s@[j] == s@[0],
        decreases s.len() - i
    {
        if s@[i] != s@[0] {
            proof {
                let spec_i = i as int;
                let spec_j = 0 as int;
                assert(s@[spec_i] != s@[spec_j]);
                assert(0 <= spec_i < s.len());
                assert(0 <= spec_j < s.len());
                assert(spec_i != spec_j);
            }
            return false;
        }
        i = i + 1;
    }
    
    proof {
        assert(s.len() > 0);
        assert forall|j: int| 0 <= j < s.len() implies s@[j] == s@[0] by {
            // This follows from the loop invariant at termination
        }
        lemma_all_same_from_first(s);
    }
    return true;
}
// </vc-code>

}
fn main() {}