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
/* helper modified by LLM (iteration 5): seq vowels count alias */
spec fn seq_vowels_count(s: Seq<char>) -> (ret: nat) { vowels(s).len() }
// </vc-helpers>

// <vc-spec>
fn vowels_count(s: &str) -> (ret: u32)

    requires
        s@.len() <= u32::MAX,

    ensures
        inner_expr_vowels_count(s, ret),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix subrange index type mismatch by casting nat to int */
    let mut result: u32 = 0u32;
    // Count vowels (a,e,i,o,u) at runtime without calling spec functions
    for c in s.chars() {
        if c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u'
            || c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U' {
            result = result + 1;
        }
    }
    let add = if s.len() > 0 {
        let last = s.chars().last().unwrap();
        if last == 'y' || last == 'Y' { 1u32 } else { 0u32 }
    } else { 0u32 };
    result = result + add;
    proof {
        let seq: Seq<char> = s@;
        let len: nat = seq.len();
        let mut i: nat = 0;
        let mut gc: nat = 0;
        while i < len
            invariant
                i <= len,
                gc == vowels(seq.subrange(0, (i as int))).len(),
            decreases len - i
        {
            // update gc to be the vowels count of seq.subrange(0, i+1) using cast to int
            gc = vowels(seq.subrange(0, ((i + 1) as int))).len();
            i = i + 1;
        }
        let add_spec: int = if len > 0 && (seq.last() == 'y' || seq.last() == 'Y') { 1int } else { 0int };
        assert((gc as u32) + if add_spec == 1int { 1u32 } else { 0u32 } == result);
        assert(inner_expr_vowels_count(s, result));
    }
    result
}
// </vc-code>

}
fn main() {}