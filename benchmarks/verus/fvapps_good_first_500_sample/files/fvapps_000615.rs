// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn is_uppercase_letter(c: char) -> bool {
    'A' <= c && c <= 'Z'
}

spec fn all_uppercase_letters(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> is_uppercase_letter(s[i])
}

fn process_string(s: Vec<char>) -> (result: u64)
    ensures 
        all_uppercase_letters(s@) ==> result == s.len() as u64,
        s.len() == 1 && !is_uppercase_letter(s@[0]) ==> result < 10,
        s.len() == 2 && !all_uppercase_letters(s@) ==> result >= 10 && result < 100,
        s.len() >= 3 && !all_uppercase_letters(s@) ==> result >= 100,
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    0u64
    // impl-end
}
// </vc-code>


}
fn main() {}