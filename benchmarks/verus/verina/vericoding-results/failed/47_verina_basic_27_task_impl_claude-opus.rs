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
/* helper modified by LLM (iteration 3): Added helper to find first occurrence index in executable code */
fn find_first_occurrence(s: &Vec<char>, c: char, end: usize) -> (result: Option<usize>)
    requires
        end <= s.len(),
        exists|i: int| 0 <= i < end && s@[i] == c,
    ensures
        match result {
            Some(idx) => idx < end && s@[idx as int] == c && 
                        forall|j: int| 0 <= j < idx ==> s@[j] != c,
            None => false,  // This case won't happen given our precondition
        },
{
    let mut i = 0;
    while i < end
        invariant
            0 <= i <= end,
            forall|j: int| 0 <= j < i ==> s@[j] != c,
    {
        if s[i] == c {
            return Some(i);
        }
        i = i + 1;
    }
    unreached()  // We know c exists in [0, end) from precondition
}

proof fn lemma_count_char_at_least_two(chars: Seq<char>, c: char, i: int, j: int)
    requires
        0 <= i < j < chars.len(),
        chars[i] == c,
        chars[j] == c,
    ensures
        count_char(chars, c) >= 2,
    decreases chars.len()
{
    if i == 0 {
        assert(chars[0] == c);
        let rest = chars.subrange(1, chars.len() as int);
        assert(rest[j - 1] == c);
        lemma_count_char_positive(rest, c, j - 1);
        assert(count_char(chars, c) == 1 + count_char(rest, c));
        assert(count_char(rest, c) >= 1);
    } else {
        let rest = chars.subrange(1, chars.len() as int);
        lemma_count_char_at_least_two(rest, c, i - 1, j - 1);
    }
}

proof fn lemma_count_char_positive(chars: Seq<char>, c: char, idx: int)
    requires
        0 <= idx < chars.len(),
        chars[idx] == c,
    ensures
        count_char(chars, c) >= 1,
    decreases chars.len()
{
    if idx == 0 {
        assert(chars[0] == c);
        assert(count_char(chars, c) >= 1);
    } else {
        let rest = chars.subrange(1, chars.len() as int);
        assert(rest[idx - 1] == c);
        lemma_count_char_positive(rest, c, idx - 1);
    }
}

proof fn lemma_no_duplicates_subrange(chars: Seq<char>, end_idx: int)
    requires
        0 <= end_idx <= chars.len(),
        has_no_duplicates_up_to(chars, end_idx),
    ensures
        has_no_duplicates(chars.subrange(0, end_idx)),
{
    assert forall|i: int, j: int| 0 <= i < j < chars.subrange(0, end_idx).len() implies
        chars.subrange(0, end_idx)[i] != chars.subrange(0, end_idx)[j] by {
        assert(chars.subrange(0, end_idx)[i] == chars[i]);
        assert(chars.subrange(0, end_idx)[j] == chars[j]);
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
    /* code modified by LLM (iteration 3): Use executable code to find first occurrence instead of choose */
    let mut seen = Set::<char>::empty();
    let mut idx = 0;
    
    while idx < s.len()
        invariant
            0 <= idx <= s.len(),
            forall|i: int| 0 <= i < idx ==> seen.contains(s@[i]),
            forall|c: char| seen.contains(c) ==> exists|i: int| 0 <= i < idx && s@[i] == c,
            has_no_duplicates_up_to(s@, idx as int),
    {
        let c = s[idx];
        
        if seen.contains(c) {
            // Found first repeated character - find its first occurrence
            let first_idx_opt = find_first_occurrence(s, c, idx);
            
            match first_idx_opt {
                Some(first_idx) => {
                    assert(s@[first_idx as int] == c);
                    assert(s@[idx as int] == c);
                    assert(first_idx < idx);
                    
                    proof {
                        lemma_count_char_at_least_two(s@, c, first_idx as int, idx as int);
                        assert(second_occurrence_exists(s@, c));
                        assert(forall|j: int| 0 <= j < first_idx ==> s@[j] != c);
                        // The spec's first_occurrence_index will be first_idx
                        assert(first_occurrence_index(s@, c) == first_idx as int);
                        let second_idx = choose|j: int| first_idx as int < j < s@.len() && s@[j] == c;
                        assert(second_idx <= idx as int);
                        assert(has_no_duplicates_up_to(s@, idx as int));
                        assert(has_no_duplicates_up_to(s@, second_idx));
                    }
                    
                    return Some(c);
                }
                None => {
                    unreached()  // We know c exists because seen.contains(c)
                }
            }
        }
        
        seen = seen.insert(c);
        idx = idx + 1;
    }
    
    proof {
        assert(idx == s.len());
        assert(has_no_duplicates_up_to(s@, s.len() as int));
        assert forall|i: int, j: int| 0 <= i < j < s@.len() implies s@[i] != s@[j] by {
            assert(has_no_duplicates_up_to(s@, s.len() as int));
        }
        assert(has_no_duplicates(s@));
    }
    
    None
}
// </vc-code>

}
fn main() {}