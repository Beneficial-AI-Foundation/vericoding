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
proof fn lemma_count_char_subrange(chars: Seq<char>, c: char, start: int, len: int) 
    requires 0 <= start <= start + len <= chars.len()
    ensures count_char(chars.subrange(start, start + len), c) == count_char(chars, c) - count_char(chars.subrange(0, start), c) - count_char(chars.subrange(start + len, chars.len()), c)
{
    if len == 0 {
        assert(chars.subrange(start, start + len) === Seq::empty());
        assert(count_char(chars.subrange(start, start + len), c) == 0);
    } else {
        lemma_count_char_subrange(chars, c, start, len - 1);
        lemma_count_char_subrange(chars, c, start + 1, len - 1);
    }
}

proof fn lemma_has_no_duplicates_implies(chars: Seq<char>, end_idx: int)
    requires has_no_duplicates(chars) && end_idx <= chars.len()
    ensures has_no_duplicates_up_to(chars, end_idx)
{
    assert forall|i: int, j: int| 0 <= i < j < end_idx implies #[trigger] chars[i] != #[trigger] chars[j] by {
        assert(0 <= i < j < chars.len());
    };
}

proof fn lemma_find_first_occurrence(chars: Seq<char>, c: char, start: int, end: int)
    requires 0 <= start <= end <= chars.len()
    ensures exists|i: int| start <= i < end && chars[i] == c ==> count_char(chars.subrange(start, end), c) > 0
{
    if end > start {
        if chars[start] == c {
            assert(count_char(chars.subrange(start, end), c) > 0);
        } else {
            lemma_find_first_occurrence(chars, c, start + 1, end);
        }
    }
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
    let mut seen_indices: Vec<nat> = Vec::new();
    let mut i: nat = 0;
    let chars = s@;
    
    while i < s.len()
        invariant
            0 <= i <= chars.len(),
            seen_indices@.len() == i,
            forall|idx: int| 0 <= idx < i ==> seen_indices@[idx] as int == idx,
            has_no_duplicates_up_to(chars, i)
    {
        let current_char = s[i];
        let mut j: nat = 0;
        
        while j < i
            invariant
                0 <= j <= i,
                forall|idx: int| 0 <= idx < j ==> #[trigger] chars[idx] != current_char
        {
            if s[j] == current_char {
                proof {
                    lemma_count_char_subrange(chars, current_char, 0, chars.len());
                    lemma_find_first_occurrence(chars, current_char, 0, j);
                    lemma_find_first_occurrence(chars, current_char, j + 1, i);
                    lemma_find_first_occurrence(chars, current_char, i + 1, chars.len());
                }
                return Some(current_char);
            }
            j = j + 1;
        }
        
        seen_indices.push(i);
        i = i + 1;
    }
    
    proof {
        lemma_has_no_duplicates_implies(chars, chars.len());
    }
    
    None
}
// </vc-code>

}
fn main() {}