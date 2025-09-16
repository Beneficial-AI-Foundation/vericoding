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
    /* code modified by LLM (iteration 5): Fixed nat/int type usage - removed explicit type conversions in exec code */
    let mut count: u32 = 0;
    let mut i: usize = 0;
    
    while i < s.unicode_len()
        invariant
            0 <= i <= s@.len(),
            s@.len() <= u32::MAX,
            count == vowels(s@.subrange(0, i as int)).len(),
        decreases s@.len() - i
    {
        let c = s.get_char(i);
        if c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || 
           c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U' {
            count = count + 1;
        }
        i = i + 1;
    }
    
    if s.unicode_len() > 0 {
        let last = s.get_char(s.unicode_len() - 1);
        if last == 'y' || last == 'Y' {
            count = count + 1;
        }
    }
    
    count
}
// </vc-code>

}
fn main() {}