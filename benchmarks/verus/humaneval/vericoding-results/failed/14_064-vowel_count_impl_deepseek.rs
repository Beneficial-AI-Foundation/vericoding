// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_vowel(c: char) -> (ret:bool) {
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I'
        || c == 'O' || c == 'U'
}

spec fn vowels(s: Seq<char>) -> (ret:Seq<char>) {
    s.filter(|c| is_vowel(c))
}

spec fn inner_expr_vowels_count(s: &str, ret: u32) -> (result:bool) {
    ret == vowels(s@).len() + if (s@.len() > 0 && (s@.last() == 'y' || s@.last() == 'Y')) {
        1int

    } else {
        0int
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed nat comparison in helper */
spec fn chars_len_nat(chars: &Vec<char>) -> (len: nat) {
    chars@.len()
}
// </vc-helpers>

// <vc-spec>
fn vowels_count(s: &str) -> (ret: u32)

    requires
        s@.len() <= u32::MAX,

    ensures
        inner_expr_vowels_count(s, ret),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed nat comparison using helper */
{
    let mut count: u32 = 0;
    let chars: Vec<char> = s.chars().collect();
    let n = chars.len() as u32;
    
    let mut i: u32 = 0;
    while i < n
        invariant
            count == vowels(chars@.subrange(0, i as int)).len(),
            0 <= i <= n,
    {
        let c = chars[i as usize];
        if is_vowel(c) {
            count += 1u32;
        }
        i += 1;
    }
    
    let len_nat = chars_len_nat(&chars);
    if len_nat > 0 && (chars@.last() == 'y' || chars@.last() == 'Y') {
        count += 1u32;
    }
    
    count
}
// </vc-code>

}
fn main() {}