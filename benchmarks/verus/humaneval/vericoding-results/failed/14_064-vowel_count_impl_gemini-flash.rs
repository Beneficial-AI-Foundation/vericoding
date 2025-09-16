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
/* helper modified by LLM (iteration 5): Removed helper function (not needed). */
// </vc-helpers>

// <vc-spec>
fn vowels_count(s: &str) -> (ret: u32)

    requires
        s@.len() <= u32::MAX,

    ensures
        inner_expr_vowels_count(s, ret),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fix for type mismatches, `subsequence` error. */
{
    let s_seq = s@;
    let mut count: u32 = 0;
    let mut i: nat = 0nats();

    while i < s_seq.len()
        invariant 
            count == vowels(s_seq.subsequence(0, i as int)).len(),
            i <= s_seq.len(),
            s_seq.len() <= u32::MAX,
        decreases s_seq.len() - i,
    {
        let c: char = s_seq.index(i as int);
        if is_vowel(c) {
            count = count + 1;
        }
        i = (i + 1) as nat;
    }

    if s_seq.len() > 0 && (s_seq.last() == 'y' || s_seq.last() == 'Y') {
        count = count + 1;
    }
    count
}
// </vc-code>

}
fn main() {}