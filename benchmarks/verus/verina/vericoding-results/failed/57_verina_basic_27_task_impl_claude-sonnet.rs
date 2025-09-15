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
proof fn lemma_count_char_positive(chars: Seq<char>, c: char, i: int)
    requires 0 <= i < chars.len() && chars[i] == c
    ensures count_char(chars, c) >= 1
    decreases chars.len()
{
    if chars.len() == 0 {
    } else if chars[0] == c {
    } else {
        lemma_count_char_positive(chars.subrange(1, chars.len() as int), c, i - 1);
    }
}

proof fn lemma_no_duplicates_up_to_monotonic(chars: Seq<char>, i: int, j: int)
    requires 0 <= i <= j <= chars.len()
    requires has_no_duplicates_up_to(chars, j)
    ensures has_no_duplicates_up_to(chars, i)
{
}

proof fn lemma_first_occurrence_properties(chars: Seq<char>, c: char)
    requires count_char(chars, c) >= 1
    ensures {
        let first_idx = first_occurrence_index(chars, c);
        0 <= first_idx < chars.len() && chars[first_idx] == c
    }
{
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
    let mut seen: Vec<char> = Vec::new();
    let mut i: usize = 0;
    
    while i < s.len()
        invariant 
            0 <= i <= s.len(),
            has_no_duplicates_up_to(s@, i as int),
            forall|k: int| 0 <= k < i ==> seen@.contains(s@[k]),
            has_no_duplicates(seen@)
    {
        let c = s[i];
        
        if seen.contains(&c) {
            proof {
                lemma_count_char_positive(s@, c, i as int);
                lemma_first_occurrence_properties(s@, c);
            }
            return Some(c);
        }
        
        seen.push(c);
        i += 1;
    }
    
    proof {
        assert(has_no_duplicates_up_to(s@, s.len() as int));
        assert(has_no_duplicates(s@));
    }
    
    None
}
// </vc-code>

}
fn main() {}