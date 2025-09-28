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
/* helper modified by LLM (iteration 3): Added spec fn as_set to link exec seen_exec to ghost seen */
spec fn as_set(s: Seq<char>) -> Set<char> {
    Set::new(|c: char| exists|i: int| 0 <= i < s.len() && #[trigger] s[i] == c)
}

/* helper modified by LLM (iteration 5): Fixed unsupported char::from_u32 by using u8 arithmetic and direct cast to char */
fn to_lower_exec(c: char) -> (result: char)
    ensures
        result == to_lower_char(c),
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
/* code modified by LLM (iteration 5): Maintained implementation after fixing compilation error in helper */
{
    let mut seen_exec: Vec<char> = Vec::new();
    let ghost mut seen: Set<char> = Set::empty();
    let mut count = 0;
    let chars: Vec<char> = s.chars().collect();
    let mut i = 0;
    proof {
        assert(chars@ == s@);
    }
    let ghost mut ghost_idx: int = 0;
    while i < chars.len()
        invariant
            ghost_idx == i as int,
            seen == as_set(seen_exec@),
            seen == char_set_from_string(chars@.take(ghost_idx)),
            0 <= ghost_idx <= chars@.len(),
        decreases chars@.len() - ghost_idx
    {
        let c = chars[i];
        let lc = to_lower_exec(c);
        proof {
            seen = seen.insert(lc);
        }
        if !seen_exec.contains(&lc) {
            seen_exec.push(lc);
            count += 1;
        }
        proof {
            ghost_idx = ghost_idx + 1;
        }
        i += 1;
    }
    proof {
        assert(seen == char_set_from_string(s@));
        assert(count == seen.len());
    }
    count
}
// </vc-code>


}

fn main() {}