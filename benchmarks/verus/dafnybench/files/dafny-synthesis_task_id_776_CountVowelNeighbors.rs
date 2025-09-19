// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_vowel(c: char) -> bool {
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' ||
    c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn count_vowel_neighbors(s: &str) -> (count: u8)
    ensures 
        count as int >= 0 &&
        count as int == Set::new(|i: int| 1 <= i < s@.len() - 1 && 
                          is_vowel(s@[i-1]) && 
                          is_vowel(s@[i+1])).len(),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}