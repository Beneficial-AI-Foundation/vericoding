// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): checks if pattern char matches a string char (supports '?') */
fn is_match_char(c: char, pc: char) -> bool {
    pc == c || pc == '?'
}
// </vc-helpers>

// <vc-spec>
fn match_strings(s: &str, p: &str) -> (result: bool)
    requires s@.len() == p@.len(),
    ensures
        result == (forall|n: int| 0 <= n < s@.len() ==> 
            (s@.index(n) == p@.index(n) || p@.index(n) == '?' as u8)),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterate using int indices and helper for chars, convert len to int */
    let n: int = s@.len() as int;
    let mut i: int = 0 as int;
    let mut ok: bool = true;
    while i < n
        invariant
            0 <= i,
            i <= n,
            ok == (forall|j: int| 0 <= j && j < i ==> is_match_char(s@.index(j), p@.index(j))),
        decreases n - i
    {
        if is_match_char(s@.index(i), p@.index(i)) {
            i = i + (1 as int);
        } else {
            ok = false;
            i = i + (1 as int);
        }
    }
    ok
}
// </vc-code>

}
fn main() {}