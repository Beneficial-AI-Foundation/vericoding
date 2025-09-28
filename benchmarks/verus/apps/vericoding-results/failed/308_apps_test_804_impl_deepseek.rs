// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(s: Seq<char>, k: int) -> bool {
    1 <= k <= 26 && 1 <= s.len() <= 1000 && 
    forall|i: int| 0 <= i < s.len() ==> 'a' <= #[trigger] s[i] <= 'z'
}

spec fn unique_chars(s: Seq<char>) -> Set<char> {
    s.to_set()
}

spec fn min_changes(s: Seq<char>, k: int) -> int {
    let unique = unique_chars(s);
    if k <= unique.len() { 0 } else { k - unique.len() }
}

spec fn is_impossible(s: Seq<char>, k: int) -> bool {
    s.len() < k
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_set_size_unique_chars(s: Seq<char>)
    ensures
        |unique_chars(s)| <= s.len(),
{
    assert(|s.to_set()| <= s.len());
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>, k: i8) -> (result: String)
    requires valid_input(s@, k as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed compilation error in lambda syntax */
    if (k as usize) > s.len() {
        return "IMPOSSIBLE".to_string();
    }
    
    let mut seen = std::collections::HashSet::new();
    let mut unique_count = 0;
    let mut i = 0;
    
    while i < s.len()
        invariant
            i <= s.len(),
            seen@ == unique_chars(s@.subrange(0, i as int)),
            unique_count == seen.len(),
    {
        if !seen.contains(&s[i]) {
            seen.insert(s[i]);
            unique_count += 1;
        }
        i += 1;
    }
    
    let required_changes = if (k as usize) > unique_count { (k as usize) - unique_count } else { 0 };
    
    let mut result = s.clone();
    let mut changes_made = 0;
    let mut char_index = 0;
    let mut next_char = 'a';
    
    while changes_made < required_changes && char_index < result.len()
        invariant
            changes_made <= required_changes,
            char_index <= result.len(),
            result@.len() == s@.len(),
    {
        if !seen.contains(&result[char_index]) {
            result[char_index] = next_char;
            changes_made += 1;
            next_char = (next_char as u8 + 1) as char;
            if next_char > 'z' { next_char = 'a'; }
        }
        char_index += 1;
    }
    
    String::from_iter(result)
}
// </vc-code>


}

fn main() {}