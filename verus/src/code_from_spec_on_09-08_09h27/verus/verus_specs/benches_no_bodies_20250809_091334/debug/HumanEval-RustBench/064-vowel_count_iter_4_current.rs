use vstd::prelude::*;

verus! {

spec fn is_vowel(c: char) -> (ret:bool) {
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I'
        || c == 'O' || c == 'U'
}
// pure-end

spec fn vowels(s: Seq<char>) -> (ret:Seq<char>) {
    s.filter(|c| is_vowel(c))
}
// pure-end

spec fn inner_expr_vowels_count(s: &str, ret: u32) -> (ret:bool) {
    ret == vowels(s@).len() + if (s@.len() > 0 && (s@.last() == 'y' || s@.last() == 'Y')) {
        1int

    } else {
        0int
    }
}
// pure-end

fn vowels_count(s: &str) -> (ret: u32)
    // pre-conditions-start
    requires
        s@.len() <= u32::MAX,
    // pre-conditions-end
    // post-conditions-start
    ensures
        inner_expr_vowels_count(s, ret),
    // post-conditions-end
{
    let mut count: u32 = 0;
    let mut i: usize = 0;
    
    /* code modified by LLM (iteration 1): use s@.len() as usize for exec length and proper character access */
    let len = s@.len() as usize;
    while i < len
        invariant
            i <= s@.len(),
            count == vowels(s@.subrange(0, i as int)).len(),
            count <= u32::MAX,
            len == s@.len(),
    {
        let c = s@[i as int];
        if is_vowel(c) {
            count = count + 1;
        }
        i = i + 1;
    }
    
    /* code modified by LLM (iteration 1): use s@.len() and s@.last() for proper character access */
    if s@.len() > 0 {
        let last_char = s@.last();
        if last_char == 'y' || last_char == 'Y' {
            count = count + 1;
        }
    }
    
    count
}

}
fn main() {}