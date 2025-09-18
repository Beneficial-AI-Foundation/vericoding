// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_char(chars: Seq<char>, c: char) -> nat 
    decreases chars.len()
{
    if chars.len() == 0 {
        0
    } else if chars[0] == c {
        1 + count_char(chars.subrange(1, chars.len() as int), c)
    } else {
        count_char(chars.subrange(1, chars.len() as int), c)
    }
}

spec fn has_no_duplicates_up_to(chars: Seq<char>, end_idx: int) -> bool {
    forall|i: int, j: int| 0 <= i < j < end_idx ==> #[trigger] chars[i] != #[trigger] chars[j]
}

spec fn has_no_duplicates(chars: Seq<char>) -> bool {
    forall|i: int, j: int| 0 <= i < j < chars.len() ==> #[trigger] chars[i] != #[trigger] chars[j]
}

spec fn first_occurrence_index(chars: Seq<char>, c: char) -> int {
    choose|i: int| 0 <= i < chars.len() && chars[i] == c
}

spec fn second_occurrence_exists(chars: Seq<char>, c: char) -> bool {
    exists|i: int, j: int| 0 <= i < j < chars.len() && #[trigger] chars[i] == c && #[trigger] chars[j] == c
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed proof block from lemma_first_occurrence_properties */
proof fn lemma_count_char_positive(chars: Seq<char>, c: char, i: int)
    requires
        0 <= i < chars.len(),
        chars[i] == c,
    ensures
        count_char(chars, c) >= 1,
    decreases chars.len()
{
    if i == 0 {
        // chars[0] == c, so count_char includes this occurrence
    } else {
        // c occurs at position i > 0, so it occurs in the tail
        lemma_count_char_positive(chars.subrange(1, chars.len() as int), c, (i - 1) as int);
    }
}

proof fn lemma_no_duplicates_up_to_extends(chars: Seq<char>, end_idx: int)
    requires
        0 <= end_idx < chars.len(),
        has_no_duplicates_up_to(chars, end_idx),
        forall|k: int| 0 <= k < end_idx ==> chars[k] != chars[end_idx],
    ensures
        has_no_duplicates_up_to(chars, end_idx + 1),
{
}

proof fn lemma_first_occurrence_properties(chars: Seq<char>, c: char)
    requires
        count_char(chars, c) >= 1,
    ensures
        0 <= first_occurrence_index(chars, c) < chars.len(),
        chars[first_occurrence_index(chars, c)] == c,
        forall|k: int| 0 <= k < first_occurrence_index(chars, c) ==> chars[k] != c,
{
    let idx = first_occurrence_index(chars, c);
    assert(0 <= idx < chars.len() && chars[idx] == c);
    assert(forall|k: int| 0 <= k < idx ==> chars[k] != c);
}
// </vc-helpers>

// <vc-spec>
fn find_first_repeated_char(s: &Vec<char>) -> (result: Option<char>)
    ensures match result {
        Some(c) => {
            let chars = s@;
            count_char(chars, c) >= 2 &&
            second_occurrence_exists(chars, c) &&
            {
                let first_idx = first_occurrence_index(chars, c);
                let second_idx = choose|j: int| first_idx < j < chars.len() && chars[j] == c;
                has_no_duplicates_up_to(chars, second_idx)
            }
        },
        None => {
            has_no_duplicates(s@)
        }
    }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): simplified implementation without nested loop */
    let mut i = 0;
    let mut seen_chars: Vec<char> = Vec::new();
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            seen_chars.len() == i,
            forall|k: int| 0 <= k < i ==> seen_chars@[k] == s@[k],
            has_no_duplicates_up_to(s@, i as int),
        decreases s.len() - i
    {
        let current_char = s[i];
        
        if seen_chars.contains(&current_char) {
            proof {
                assert(exists|k: int| 0 <= k < i && s@[k] == current_char);
                assert(count_char(s@, current_char) >= 2);
                assert(second_occurrence_exists(s@, current_char));
            }
            return Some(current_char);
        }
        
        seen_chars.push(current_char);
        i += 1;
    }
    
    None
}
// </vc-code>

}
fn main() {}