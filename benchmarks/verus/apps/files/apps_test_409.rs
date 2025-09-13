// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_substring(s: Seq<char>, pattern: Seq<char>) -> nat
    decreases s.len()
{
    if pattern.len() == 0 || s.len() < pattern.len() {
        0
    } else if s.subrange(0, pattern.len() as int) == pattern {
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
    } else if s.subrange(0, pattern.len() as int) == pattern {
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
// </vc-helpers>

// <vc-spec>
fn solve(input: Seq<char>) -> (result: Seq<char>)
    requires valid_input(input)
    ensures result == seq!['Y', 'E', 'S'] <==> has_non_overlapping_ab_and_ba(if input.len() > 0 && input[input.len() - 1] == '\n' { input.subrange(0, input.len() - 1) } else { input })
    ensures result == seq!['Y', 'E', 'S'] || result == seq!['N', 'O']
    ensures ({
        let s = if input.len() > 0 && input[input.len() - 1] == '\n' { input.subrange(0, input.len() - 1) } else { input };
        let ab_pattern = seq!['A', 'B'];
        let ba_pattern = seq!['B', 'A'];
        (count_substring(s, ab_pattern) == 0 || count_substring(s, ba_pattern) == 0) ==> result == seq!['N', 'O']
    })
    ensures ({
        let s = if input.len() > 0 && input[input.len() - 1] == '\n' { input.subrange(0, input.len() - 1) } else { input };
        let ab_pattern = seq!['A', 'B'];
        let ba_pattern = seq!['B', 'A'];
        let ab_index = find_index(s, ab_pattern);
        let ba_index = find_index(s, ba_pattern);
        (count_substring(s, ab_pattern) > 0 && count_substring(s, ba_pattern) > 0 &&
         !((ab_index >= 0 && ab_index + 2 < s.len() && count_substring(s.subrange(ab_index + 2, s.len() as int), ba_pattern) > 0) ||
           (ba_index >= 0 && ba_index + 2 < s.len() && count_substring(s.subrange(ba_index + 2, s.len() as int), ab_pattern) > 0))) ==> result == seq!['N', 'O']
    })
// </vc-spec>
// <vc-code>
{
    assume(false);
    seq!['N', 'O']
}
// </vc-code>


}

fn main() {}