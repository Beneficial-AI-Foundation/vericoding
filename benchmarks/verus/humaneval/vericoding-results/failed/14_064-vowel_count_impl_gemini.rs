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
/* helper modified by LLM (iteration 5): No functional change, comment updated. */
fn exec_is_vowel(c: char) -> (ret: bool)
    ensures ret == is_vowel(c)
{
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I'
        || c == 'O' || c == 'U'
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
{
    /* code modified by LLM (iteration 5): Fixed compilation errors by removing an obsolete lemma and correcting a module path. */
    let chars_vec: Vec<char> = s.chars().collect();
    proof {
        vstd::vec_lib::lemma_vec_from_iterator(s.chars());
    }

    let mut count: u32 = 0;
    let mut i: usize = 0;
    while i < chars_vec.len()
        invariant
            i <= chars_vec.len(),
            chars_vec@ == s@,
            count as int == vowels(s@.subrange(0, i as int)).len(),
        decreases chars_vec.len() - i
    {
        let c = chars_vec[i];
        if exec_is_vowel(c) {
            count = count + 1;
        }
        i = i + 1;
    }

    let mut result = count;
    let vec_len = chars_vec.len();
    if vec_len > 0 {
        let last_char = chars_vec[vec_len - 1];
        if last_char == 'y' || last_char == 'Y' {
            result = result + 1;
        }
        proof {
            assert(s@.len() == chars_vec.len());
            assert(s@.last() == chars_vec@[(vec_len - 1) as int]);
            assert(s@.last() == last_char);
        }
    }
    
    result
}
// </vc-code>

}
fn main() {}