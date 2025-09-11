// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn reverse_string(s: &Vec<char>) -> (result: Vec<char>)
    ensures
        result@.len() == s@.len(),
        forall|i: int| 0 <= i < s@.len() ==> result@[i] == s@[s@.len() - 1 - i],
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}