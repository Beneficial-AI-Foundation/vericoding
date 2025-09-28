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

// </vc-helpers>

// <vc-spec>
fn count_distinct_characters(s: &str) -> (count: usize)
    ensures 
        count <= s@.len(),
        count == char_set_from_string(s@).len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Using get_char() method instead of chars().collect() to avoid unsupported iterator methods */
    let mut seen = Set::<char>::empty();
    let mut count: usize = 0;
    let mut i: usize = 0;
    
    while i < s@.len()
        invariant
            0 <= i <= s@.len(),
            count <= i,
            count == seen.len(),
            seen == Set::new(|c: char| exists|j: int| 0 <= j < i && to_lower_char(s@[j]) == c),
    {
        let c = s@[i as int];
        let lower_c = if 'A' <= c && c <= 'Z' {
            ((c as u8 - 'A' as u8 + 'a' as u8) as char)
        } else {
            c
        };
        
        if !seen.contains(lower_c) {
            seen = seen.insert(lower_c);
            count = count + 1;
        }
        
        i = i + 1;
    }
    
    proof {
        assert(seen == char_set_from_string(s@));
    }
    
    count
}
// </vc-code>


}

fn main() {}