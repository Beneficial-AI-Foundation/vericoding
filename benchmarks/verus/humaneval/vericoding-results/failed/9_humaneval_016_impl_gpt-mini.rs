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
/* helper modified by LLM (iteration 5): each char's lowercase is in the char set */
proof fn char_set_member(s: Seq<char>, i: int)
    requires
        0 <= i && i < s.len(),
    ensures
        char_set_from_string(s).contains(to_lower_char(s[i])),
{
    // witness i demonstrates existence for the set definition
    assert(exists|j: int| 0 <= j && j < s.len() && #[trigger] to_lower_char(s[j]) == to_lower_char(s[i]));
}

// </vc-helpers>

// <vc-spec>
fn count_distinct_characters(s: &str) -> (count: usize)
    ensures 
        count <= s@.len(),
        count == char_set_from_string(s@).len(),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): iterate over input chars and collect unique lowercase chars */
{
    let mut seen: Vec<char> = Vec::new();
    for ch in s.chars() {
        let lc: char = to_lower_char(ch);
        let mut found: bool = false;
        let mut k: usize = 0;
        while k < seen.len()
            invariant
                k <= seen.len(),
            decreases seen.len() - k,
        {
            if seen[k] == lc {
                found = true;
            }
            k += 1;
        }
        if !found {
            seen.push(lc);
        }
    }

    seen.len()
}

// </vc-code>


}

fn main() {}