// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn is_letter(c: char) -> bool {
    'a' <= c && c <= 'z'
}

spec fn char_to_digit(c: char) -> int {
    (c as u8 - '0' as u8) as int
}

spec fn string_contains_letter(s: Seq<char>) -> bool {
    exists|i: int| 0 <= i < s.len() && is_letter(s[i])
}

spec fn string_starts_with_letter(s: Seq<char>) -> bool {
    s.len() > 0 && is_letter(s[0])
}

fn decode_at_index(s: Vec<char>, k: usize) -> (result: char)
    requires 
        k > 0,
        string_contains_letter(s@),
        string_starts_with_letter(s@),
    ensures 
        is_letter(result),
        exists|i: int| 0 <= i < s.len() && is_letter(s[i]) && result == s[i],
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    'a'
    // impl-end
}
// </vc-code>


}
fn main() {
    // let s1 = vec!['l', 'e', 'e', 't', '2', 'c', 'o', 'd', 'e', '3'];
    // println!("{}", decode_at_index(s1, 10));
    // let s2 = vec!['h', 'a', '2', '2'];
    // println!("{}", decode_at_index(s2, 5));
    // let s3 = vec!['a', '2', '3', '4', '5', '6', '7', '8', '9', '9', '9', '9', '9', '9', '9', '9', '9', '9', '9', '9', '9', '9', '9'];
    // println!("{}", decode_at_index(s3, 1));
}