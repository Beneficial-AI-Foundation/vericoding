// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn count_substring(s: Seq<char>, pattern: Seq<char>) -> nat 
    decreases s.len()
{
    if pattern.len() == 0 || s.len() < pattern.len() {
        0
    } else if s.subrange(0, pattern.len() as int) =~= pattern {
        1 + count_substring(s.subrange(1, s.len() as int), pattern)
    } else {
        count_substring(s.subrange(1, s.len() as int), pattern)
    }
}

spec fn find_index(s: Seq<char>, pattern: Seq<char>) -> int 
    decreases s.len()
{
    if pattern.len() == 0 || s.len() < pattern.len() {
        -1
    } else if s.subrange(0, pattern.len() as int) =~= pattern {
        0
    } else {
        let rest = find_index(s.subrange(1, s.len() as int), pattern);
        if rest == -1 { -1 } else { 1 + rest }
    }
}

spec fn has_non_overlapping_ab_and_ba(s: Seq<char>) -> bool {
    let ab_pattern = seq!['A', 'B'];
    let ba_pattern = seq!['B', 'A'];
    let ab_index = find_index(s, ab_pattern);
    let ba_index = find_index(s, ba_pattern);

    (ab_index >= 0 && ba_index >= 0) &&
    (
        (ab_index >= 0 && ab_index + 2 < s.len() && count_substring(s.subrange(ab_index + 2, s.len() as int), ba_pattern) > 0) ||
        (ba_index >= 0 && ba_index + 2 < s.len() && count_substring(s.subrange(ba_index + 2, s.len() as int), ab_pattern) > 0)
    )
}

spec fn valid_input(input: Seq<char>) -> bool {
    input.len() >= 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [no helpers needed] */
// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<char>) -> (result: Vec<char>)
    requires valid_input(input@)
    ensures 
        result@ == seq!['Y', 'E', 'S'] || result@ == seq!['N', 'O'],
        has_non_overlapping_ab_and_ba(input@) <==> result@ == seq!['Y', 'E', 'S']
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): [cast `s_seq.len()` to `int` within ghost code for subrange operations and count_substring calls] */
{
    let s_seq = input@;
    let ab_pattern = seq!['A', 'B'];
    let ba_pattern = seq!['B', 'A'];

    let ab_index = find_index(s_seq, ab_pattern);
    let ba_index = find_index(s_seq, ba_pattern);

    if ab_index >= 0 && ba_index >= 0 {
        // Check for 'AB' then 'BA'
        let ab_then_ba = ab_index + 2 <= (s_seq.len() as int) && count_substring(s_seq.subrange(ab_index + 2, s_seq.len() as int), ba_pattern) > 0; // Fixed: Use s_seq.len() as int

        // Check for 'BA' then 'AB'
        let ba_then_ab = ba_index + 2 <= (s_seq.len() as int) && count_substring(s_seq.subrange(ba_index + 2, s_seq.len() as int), ab_pattern) > 0; // Fixed: Use s_seq.len() as int

        if ab_then_ba || ba_then_ab {
            return vec!['Y', 'E', 'S'];
        } else {
            return vec!['N', 'O'];
        }
    } else {
        return vec!['N', 'O'];
    }
}
// </vc-code>


}

fn main() {}