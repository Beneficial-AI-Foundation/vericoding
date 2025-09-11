// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn find_all_occurrences(text: &str, pattern: &str) -> (offsets: Ghost<Set<nat>>)
    ensures 
        forall|i: nat| offsets@.contains(i) ==> i + pattern@.len() <= text@.len(),
        forall|i: nat| 0 <= i && i + pattern@.len() <= text@.len() 
                      ==> (text@.subrange(i as int, (i + pattern@.len()) as int) == pattern@) == offsets@.contains(i)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}