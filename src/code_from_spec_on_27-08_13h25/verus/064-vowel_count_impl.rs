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
// No changes needed in helpers for this fix
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
    let mut i: usize = 0;
    let s_len: usize = s@.len();

    while i < s_len
        invariant
            s@.len() <= u32::MAX,
            i <= s_len,
            count <= i as u32,
    {
        let c = s.chars().nth(i).unwrap();
        if is_vowel(c) {
            count = count + 1;
        }
        i = i + 1;
    }

    if s_len > 0 {
        let last_char = s@.last();
        if last_char == 'y' || last_char == 'Y' {
            count = count + 1;
        }
    }

    count
}
// </vc-code>

}
fn main() {}