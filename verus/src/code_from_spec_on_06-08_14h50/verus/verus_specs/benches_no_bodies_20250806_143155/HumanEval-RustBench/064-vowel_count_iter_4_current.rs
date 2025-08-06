use vstd::prelude::*;

verus! {

spec fn is_vowel(c: char) -> (ret:bool) {
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I'
        || c == 'O' || c == 'U'
}
// pure-end

/* code modified by LLM (iteration 3): Added executable version of is_vowel function */
fn is_vowel_exec(c: char) -> (ret: bool)
    ensures ret == is_vowel(c)
{
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I'
        || c == 'O' || c == 'U'
}

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
    
    /* code modified by LLM (iteration 3): Changed s.len() to s@.len() for proper Verus string handling */
    while i < s@.len()
        invariant
            i <= s@.len(),
            count <= u32::MAX,
            count == vowels(s@.subrange(0, i as int)).len(),
    {
        let c = s.get_char(i);
        if is_vowel_exec(c) {
            count = count + 1;
        }
        i = i + 1;
    }
    
    /* code modified by LLM (iteration 3): Changed s.len() to s@.len() for proper Verus string handling */
    if s@.len() > 0 {
        let last_char = s.get_char(s@.len() - 1);
        if last_char == 'y' || last_char == 'Y' {
            count = count + 1;
        }
    }
    
    count
}

}
fn main() {}