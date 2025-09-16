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
/* helper modified by LLM (iteration 5): Added helper to get character sequence using as_bytes and casting */
fn get_chars(s: &str) -> (chars: Vec<char>)
    ensures
        chars@.len() == s@.len(),
        forall|i: int| 0 <= i < s@.len() ==> chars@[i] == s@[i],
{
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < s.len()
        invariant
            i <= s@.len(),
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == s@[j],
    {
        result.push(s@[i as int]);
        i = i + 1;
    }
    
    result
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
    /* code modified by LLM (iteration 5): Use string indexing with @ operator instead of unicode_codepoints() */
    let mut count = 0u32;
    let mut i = 0usize;
    
    while i < s.len()
        invariant
            i <= s@.len(),
            count <= i,
            count == vowels(s@.subrange(0, i as int)).len(),
    {
        let c = s@[i as int];
        if is_vowel(c) {
            count = count + 1;
        }
        i = i + 1;
    }
    
    if s.len() > 0 {
        let last_char = s@[s@.len() - 1];
        if last_char == 'y' || last_char == 'Y' {
            count = count + 1;
        }
    }
    
    count
}
// </vc-code>

}
fn main() {}