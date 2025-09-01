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
spec fn inner_expr_vowels_count(s: &str, ret: u32) -> (ret: bool) {
    ret == ((vowels(s@).len() as int) + if (s@.len() > 0 && (s@.last() == 'y' || s@.last() == 'Y')) {
        1int
    } else {
        0int
    }) as u32
}
// pure-end
// pure-end
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
    let seq = s@;
    let len = seq.len() as int;
    let mut count = 0u32;
    let mut i = 0;
    while i < len
        invariant
            i <= len,
            (count as int) == (vowels(seq.subrange(0, i)).len() as int),
            count <= (len as int) as u32,
    {
        if is_vowel(seq.index(i)) {
            count = count + 1;
        }
        i = i + 1;
    }
    if len > 0 && (seq.index(len - 1) == 'y' || seq.index(len - 1) == 'Y') {
        count = count + 1;
    }
    count
}
// </vc-code>

fn main() {}
}