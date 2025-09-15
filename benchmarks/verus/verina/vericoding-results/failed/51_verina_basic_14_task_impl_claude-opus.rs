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
    /* code modified by LLM (iteration 5): Use chars() iterator to avoid type conversion issues */
    let mut i: usize = 0;
    let chars = s.chars();
    for c in chars {
        if c == 'z' || c == 'Z' {
            return true;
        }
        i = i + 1;
    }
    false
}
// </vc-code>

}
fn main() {}