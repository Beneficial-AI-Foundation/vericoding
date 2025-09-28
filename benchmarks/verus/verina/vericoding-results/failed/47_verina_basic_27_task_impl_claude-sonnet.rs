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
/* helper modified by LLM (iteration 5): removed trigger annotations to fix compilation error */
proof fn lemma_count_char_positive_implies_exists(chars: Seq<char>, c: char)
    requires count_char(chars, c) >= 2
    ensures second_occurrence_exists(chars, c)
    decreases chars.len()
{
    if chars.len() == 0 {
        assert(count_char(chars, c) == 0);
        assert(false);
    } else if chars[0] == c {
        let rest = chars.subrange(1, chars.len() as int);
        if count_char(rest, c) >= 1 {
            lemma_count_char_implies_exists(rest, c);
            assert(exists|i: int| 1 <= i < chars.len() && chars[i] == c);
        }
    } else {
        let rest = chars.subrange(1, chars.len() as int);
        lemma_count_char_positive_implies_exists(rest, c);
    }
}

proof fn lemma_count_char_implies_exists(chars: Seq<char>, c: char)
    requires count_char(chars, c) >= 1
    ensures exists|i: int| 0 <= i < chars.len() && chars[i] == c
    decreases chars.len()
{
    if chars.len() == 0 {
        assert(count_char(chars, c) == 0);
        assert(false);
    } else if chars[0] == c {
        assert(chars[0] == c);
    } else {
        let rest = chars.subrange(1, chars.len() as int);
        lemma_count_char_implies_exists(rest, c);
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
    /* code modified by LLM (iteration 5): removed trigger annotations to fix compilation error */
    let mut seen = Vec::new();
    let mut i = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            has_no_duplicates_up_to(s@, i as int),
            forall|k: int| 0 <= k < seen.len() ==> exists|j: int| 0 <= j < i && s[j] == seen[k],
            forall|j: int| 0 <= j < i ==> exists|k: int| 0 <= k < seen.len() && seen[k] == s[j]
        decreases s.len() - i
    {
        let current_char = s[i];
        let mut found = false;
        let mut j = 0;
        
        while j < seen.len()
            invariant
                0 <= j <= seen.len(),
                found == exists|k: int| 0 <= k < j && seen[k] == current_char
            decreases seen.len() - j
        {
            if seen[j] == current_char {
                found = true;
                proof {
                    assert(exists|k: int| 0 <= k < i && s[k] == current_char);
                    assert(s[i as int] == current_char);
                    assert(second_occurrence_exists(s@, current_char));
                    lemma_count_char_positive_implies_exists(s@, current_char);
                }
                return Some(current_char);
            }
            j += 1;
        }
        
        if !found {
            seen.push(current_char);
        }
        
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