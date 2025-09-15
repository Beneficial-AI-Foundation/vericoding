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
    /* code modified by LLM (iteration 4): Added decreases clauses to both loops for termination proof */
    let mut i: usize = 0;
    while i < s.len()
        decreases (s.len() - i@)
        invariant has_no_duplicates_up_to(s@, i as int)
    {
        let c = s[i];
        let mut previously_seen = false;
        let mut k: usize = 0;
        while k < i
            decreases (i - k@)
            invariant forall |l: int| 0 <= l < k ==> s@[l as int] != c
        {
            if s[k] == c {
                previously_seen = true;
                break;
            }
            k += 1;
        }
        if previously_seen {
            proof {
                let chars = s@;
                assert(second_occurrence_exists(chars, c));
                let first_idx = choose |j: int| 0 <= j < chars.len() && chars[j] == c;
                assert(forall |j: int| 0 <= j < chars.len() && chars[j] == c ==> first_idx <= j);
                // Since no duplicates before i, the min is the first
                let second_idx = i as int;
                assert(has_no_duplicates_up_to(chars, second_idx + 1));
                // But actual is up to where the duplicate is found
            }
            return Some(c);
        }
        // If not seen, continue
        i += 1;
    }
    proof {
        assert(has_no_duplicates(s@));
    }
    return None;
}
// </vc-code>

}
fn main() {}