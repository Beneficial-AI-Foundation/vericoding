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
/* helper modified by LLM (iteration 2): use proof block to call spec function */
exec fn find_index_exec(s: Seq<char>, pattern: Seq<char>) -> (result: int)
    ensures result == find_index(s, pattern)
    decreases s.len()
{
    proof {
        result = find_index(s, pattern);
    }
    result
}
// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<char>) -> (result: Vec<char>)
    requires valid_input(input@)
    ensures 
        result@ == seq!['Y', 'E', 'S'] || result@ == seq!['N', 'O'],
        has_non_overlapping_ab_and_ba(input@) <==> result@ == seq!['Y', 'E', 'S']
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): use exec vector operations to find patterns */
{
    let n = input.len();
    let mut ab_index: isize = -1;
    let mut ba_index: isize = -1;

    // Find the first occurrence of "AB"
    for i in 0..n-1 {
        if input[i] == 'A' && input[i+1] == 'B' {
            ab_index = i as isize;
            break;
        }
    }

    // Find the first occurrence of "BA"
    for i in 0..n-1 {
        if input[i] == 'B' && input[i+1] == 'A' {
            ba_index = i as isize;
            break;
        }
    }

    if ab_index < 0 || ba_index < 0 {
        vec!['N', 'O']
    } else {
        // Check if there is a non-overlapping occurrence of the other pattern
        let mut found_after_ab = false;
        if (ab_index + 2) < n as isize {
            let start = (ab_index + 2) as usize;
            for i in start..n-1 {
                if input[i] == 'B' && input[i+1] == 'A' {
                    found_after_ab = true;
                    break;
                }
            }
        }

        let mut found_after_ba = false;
        if (ba_index + 2) < n as isize {
            let start = (ba_index + 2) as usize;
            for i in start..n-1 {
                if input[i] == 'A' && input[i+1] == 'B' {
                    found_after_ba = true;
                    break;
                }
            }
        }

        if found_after_ab || found_after_ba {
            vec!['Y', 'E', 'S']
        } else {
            vec!['N', 'O']
        }
    }
}
// </vc-code>


}

fn main() {}