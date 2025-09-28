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
/* helper modified by LLM (iteration 5): fixed contains_char to work with spec-only types */
spec fn contains_char_spec(vec: Seq<char>, c: char) -> bool {
    exists|i: int| 0 <= i < vec.len() && vec[i] == c
}

fn contains_char(vec: &Vec<char>, c: char) -> (result: bool)
    ensures result == contains_char_spec(vec@, c)
{
    let mut i = 0;
    while i < vec.len()
        invariant
            0 <= i <= vec.len(),
            !contains_char_spec(vec@.subrange(0, i as int), c),
        decreases vec.len() - i
    {
        if vec[i] == c {
            return true;
        }
        i += 1;
    }
    false
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
/* code modified by LLM (iteration 5): simplified approach without seen vector */
{
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            has_no_duplicates_up_to(s@, i as int),
        decreases s.len() - i
    {
        let c = s[i];
        let mut j = i + 1;
        while j < s.len()
            invariant
                i + 1 <= j <= s.len(),
                forall|k: int| i < k < j ==> s@[k] != c,
            decreases s.len() - j
        {
            if s[j] == c {
                proof {
                    assert(has_no_duplicates_up_to(s@, j as int));
                }
                return Some(c);
            }
            j += 1;
        }
        i += 1;
    }
    None
}
// </vc-code>

}
fn main() {}