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
    /* code modified by LLM (iteration 5): Fix invariant bound and add assertion for precondition */
    let mut i: usize = 0;
    let mut found = false;
    let len = s.unicode_len();
    while i < len
        invariant
            0 <= i <= len,
            len == s@.len(),
            found <==> exists|j: int| 0 <= j < i && (s@[j] == 'z' || s@[j] == 'Z'),
        decreases len - i
    {
        assert(i < s@.len());
        let c = s.get_char(i);
        if c == 'z' || c == 'Z' {
            found = true;
        }
        i = i + 1;
    }
    found
}
// </vc-code>

}
fn main() {}