// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn contains_z(s: &str) -> (result: bool)
    ensures
        result <==> exists|i: int| 0 <= i < s@.len() && (s@[i] == 'z' || s@[i] == 'Z'),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): replaced nat/int types with usize and used character iterator */
    for c in s.chars() {
        if c == 'z' || c == 'Z' {
            return true;
        }
    }
    false
}
// </vc-code>

}
fn main() {}