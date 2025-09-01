use vstd::prelude::*;

verus! {

spec fn is_vowel(c: char) -> (ret:bool) {
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I'
        || c == 'O' || c == 'U'
}
// pure-end
// pure-end

spec fn vowels(s: Seq<char>) -> (ret:Seq<char>) {
    s.filter(|c| is_vowel(c))
}
// pure-end
// pure-end

spec fn inner_expr_vowels_count(s: &str, ret: u32) -> (ret:bool) {
    ret == vowels(s@).len() + if (s@.len() > 0 && (s@.last() == 'y' || s@.last() == 'Y')) {
        1int

    } else {
        0int
    }
}
// pure-end

// <vc-helpers>
#[verifier(external_body)]
#[inline(always)]
fn char_is_alpha(c: char) -> bool {
    // This is essentially `c.is_alphabetic()`
    // We use external_body because of the wide range of Unicode alphabetic characters.
    // For the purposes of this problem, we only care about 'a' through 'z' and 'A' through 'Z'.
    // `is_vowel` spec function already handles the exact vowels.
    (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
}
// </vc-helpers>

// <vc-spec>
fn vowels_count(s: &str) -> (ret: u32)
    // pre-conditions-start
    requires
        s@.len() <= u32::MAX,
    // pre-conditions-end
    // post-conditions-start
    ensures
        inner_expr_vowels_count(s, ret),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut count: u32 = 0;
    let s_len = s.len();
    let s_char_seq = s@;

    let mut i: u64 = 0;
    while i < s_len
        invariant
            i as nat <= s_char_seq.len(),
            count == vowels(s_char_seq.subsequence(0, i as int)).len(),
            s_len == s_char_seq.len(),
            i <= s_len,
            s@ == s_char_seq,
    {
        let c = s_char_seq.index(i as int);
        if is_vowel(c) {
            count = count + 1;
        }
        i = i + 1;
    }

    let mut final_count = count;

    if s_len > 0 {
        let last_char = s_char_seq.last();
        if last_char == 'y' || last_char == 'Y' {
            final_count = final_count + 1;
        }
    }

    final_count
}
// </vc-code>

fn main() {}
}