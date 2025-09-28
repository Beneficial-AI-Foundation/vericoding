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
proof fn char_set_contains_lower_eq()
    ensures
        forall |s: Seq<char>, c: char|
            char_set_from_string(s).contains(c) == exists|i: int| 0 <= i < s.len() && to_lower_char(s[i]) == c,
{
    /* helper modified by LLM (iteration 5): fix for all quantifier syntax */
    assert forall |s: Seq<char>, c: char| char_set_from_string(s).contains(c) == exists|i: int| 0 <= i < s.len() && to_lower_char(s[i]) == c by {
        assert(char_set_from_string(s).contains(c) == exists|i: int| 0 <= i < s.len() && #[trigger] to_lower_char(s[i]) == c);
    };
}

proof fn finite_char_set_len_bound()
    ensures
        forall |s: Seq<char>|
            char_set_from_string(s).finite() && char_set_from_string(s).len() <= s.len(),
{
    /* helper modified by LLM (iteration 5): maintain char set size bound */
    assert forall |s: Seq<char>| char_set_from_string(s).finite() && char_set_from_string(s).len() <= s.len() by {
        assert(char_set_from_string(s).finite());
        assert(char_set_from_string(s).len() <= s.len());
    };
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
    /* code modified by LLM (iteration 5): fix index type casting */
    let mut seen = Vec::new();
    let mut count = 0;
    let mut index: usize = 0;
    
    while index < s.len()
        invariant
            count <= index,
            count == char_set_from_string(s@.subrange(0, index)).len(),
    {
        let c = s@.index(index);
        let lower_c = to_lower_char(c);
        let mut found = false;
        let mut j: usize = 0;
        
        while j < seen.len()
            invariant
                j <= seen.len(),
                forall |k: int| 0 <= k < j ==> seen@.index(k as usize) != lower_c,
        {
            if seen@.index(j) == lower_c {
                found = true;
                break;
            }
            j += 1;
        }
        
        if !found {
            seen.push(lower_c);
            count += 1;
        }
        
        index += 1;
    }
    
    count
}
// </vc-code>


}

fn main() {}