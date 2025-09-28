// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No change needed as helper is correct. */
spec fn at_matches(text: Seq<char>, pattern: Seq<char>, i: nat) -> bool
    requires
        i + pattern.len() <= text.len(),
{
    text.subrange(i as int, (i + pattern.len()) as int) == pattern
}
// </vc-helpers>

// <vc-spec>
fn find_all_occurrences(text: &str, pattern: &str) -> (offsets: Ghost<Set<nat>>)
    ensures 
        forall|i: nat| offsets@.contains(i) ==> i + pattern@.len() <= text@.len(),
        forall|i: nat| 0 <= i && i + pattern@.len() <= text@.len() 
                      ==> (text@.subrange(i as int, (i + pattern@.len()) as int) == pattern@) == offsets@.contains(i)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Changed loop counter 'i' from usize to nat to fix a type mismatch compilation error. */
{
    let text_seq = text@;
    let pattern_seq = pattern@;

    if pattern_seq.len() > text_seq.len() {
        return Ghost(Set::empty());
    }

    let limit = text_seq.len() - pattern_seq.len();
    let mut i: nat = 0;
    let ghost mut offsets = Set::empty();

    while i <= limit
        invariant
            i <= limit + 1,
            text@ == text_seq,
            pattern@ == pattern_seq,
            forall|j: nat| offsets.contains(j) ==> j + pattern_seq.len() <= text_seq.len(),
            forall|j: nat| j < i ==> at_matches(text_seq, pattern_seq, j) == offsets.contains(j),
        decreases limit - i
    {
        proof {
            if at_matches(text_seq, pattern_seq, i) {
                offsets = offsets.insert(i);
            }
        }
        i = i + 1;
    }

    Ghost(offsets)
}
// </vc-code>

}
fn main() {}