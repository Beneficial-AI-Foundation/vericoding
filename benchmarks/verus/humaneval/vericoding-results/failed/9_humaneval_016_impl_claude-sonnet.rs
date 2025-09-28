// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn to_lower_char(c: char) -> char {
    if 'A' <= c && c <= 'Z' {
        ((c as u8 - 'A' as u8 + 'a' as u8) as char)
    } else {
        c
    }
}

spec fn char_set_from_string(s: Seq<char>) -> Set<char> {
    Set::new(|c: char| exists|i: int| 0 <= i < s.len() && #[trigger] to_lower_char(s[i]) == c)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): convert spec function to executable */
fn to_lower_char_exec(c: char) -> (result: char)
    ensures result == to_lower_char(c)
{
    if 'A' <= c && c <= 'Z' {
        ((c as u8 - 'A' as u8 + 'a' as u8) as char)
    } else {
        c
    }
}
// </vc-helpers>

// <vc-spec>
fn count_distinct_characters(s: &str) -> (count: usize)
    ensures 
        count <= s@.len(),
        count == char_set_from_string(s@).len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use usize::try_from for nat to usize conversion */
    let mut seen_chars: Set<char> = Set::empty();
    let s_bytes = s.as_bytes();
    let mut i = 0;
    
    while i < s_bytes.len()
        invariant
            0 <= i <= s_bytes.len(),
            seen_chars.finite(),
    {
        let byte_val = s_bytes[i];
        if byte_val.is_ascii() {
            let c = byte_val as char;
            let lower_c = to_lower_char_exec(c);
            seen_chars = seen_chars.insert(lower_c);
        }
        i += 1;
    }
    
    proof {
        assert(seen_chars.len() <= s@.len());
        assert(seen_chars.len() <= usize::MAX);
    }
    
    usize::try_from(seen_chars.len()).unwrap()
}
// </vc-code>


}

fn main() {}