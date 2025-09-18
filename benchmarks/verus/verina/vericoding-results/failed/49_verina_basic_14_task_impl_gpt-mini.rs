// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): predicate for checking 'z' or 'Z' */
fn is_z_or_Z(c: char) -> bool {
    c == 'z' || c == 'Z'
}

// </vc-helpers>

// <vc-spec>
fn contains_z(s: &str) -> (result: bool)
    ensures
        result <==> exists|i: int| 0 <= i < s@.len() && (s@[i] == 'z' || s@[i] == 'Z'),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterate over string using int indices and maintain found invariant */
    let mut i: int = 0;
    let mut found: bool = false;
    while i < s@.len()
        invariant
            0 <= i <= s@.len(),
            found <==> exists |j: int| 0 <= j && j < i && (s@[j] == 'z' || s@[j] == 'Z'),
        decreases s@.len() - i
    {
        if s@[i] == 'z' || s@[i] == 'Z' {
            found = true;
            i = s@.len();
        } else {
            i = i + 1;
        }
    }
    found
}

// </vc-code>

}
fn main() {}