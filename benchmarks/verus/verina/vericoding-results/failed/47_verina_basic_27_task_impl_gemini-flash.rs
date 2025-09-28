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
/* helper modified by LLM (iteration 5): This lemma is now commented out as it was not used and generated errors. It would be used if we were proving correctness about unique characters, but this problem is about the first repeated character. */
/*
proof fn lemma_no_duplicates_implies_first_occurrence_is_unique(chars: Seq<char>, c: char, i: int)
    requires
        0 <= i < chars.len(),
        chars[i] == c,
        has_no_duplicates(chars)
    ensures
        forall|j: int| 0 <= j < chars.len() && chars[j] == c ==> j == i
{
    // Proof relies directly on the definition of has_no_duplicates.
}
*/
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
/* code modified by LLM (iteration 5): Corrected `idx` type to `usize` for proper indexing, fixed type mismatches in invariants and decreases clauses, and adjusted `chars[i]` indexing to use `i as int` where `Seq` expects `int`. */
{
    let chars: Seq<char> = s@;
    let mut seen_chars: Set<char> = Set::empty();
    let mut idx: usize = 0; // Changed to usize for proper Vec indexing

    while idx < chars.len()
        invariant 
            idx <= chars.len(),
            forall|k: char| seen_chars.contains(k) ==> exists|i: int| 0 <= i < idx && chars[i as int] == k,
            forall|i: int| 0 <= i < idx ==> seen_chars.contains(chars[i as int]),
            has_no_duplicates_up_to(chars, idx as int)
        decreases chars.len() - idx
    {
        let current_char = s[idx]; // Access Vec directly with usize index
        if seen_chars.contains(current_char) {
            return Some(current_char);
        } else {
            seen_chars = seen_chars.insert(current_char);
        }
        idx = idx + 1;
    }

    proof {
        if idx == chars.len() {
            assert(has_no_duplicates_up_to(chars, chars.len() as int));
            assert(has_no_duplicates(chars));
        }
    }

    None
}
// </vc-code>

}
fn main() {}