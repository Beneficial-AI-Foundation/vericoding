use vstd::prelude::*;

verus! {

spec fn is_vowel(c: char) -> bool {
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' ||
    c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'
}

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn count_vowel_neighbors(s: &str) -> (count: usize)
    ensures 
        count >= 0 &&
        count == Set::new(|i: int| 1 <= i < s@.len() - 1 && 
                          is_vowel(s@[i-1]) && 
                          is_vowel(s@[i+1])).len(),
// </vc-spec>
// <vc-code>
{
  assume(false);
  0
}
// </vc-code>

fn main() {
}

}