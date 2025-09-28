// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(s: Seq<char>) -> bool {
    s.len() > 0 && forall|i: int| 0 <= i < s.len() ==> s[i] == 'B' || s[i] == 'W'
}

spec fn count_segments(s: Seq<char>) -> int
    decreases s.len()
{
    if s.len() <= 1 {
        1int
    } else {
        count_segments(s.subrange(0, s.len() - 1)) + 
        (if s[s.len() - 1] != s[s.len() - 2] { 1int } else { 0int })
    }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: i8)
    requires 
        valid_input(s@),
    ensures 
        result >= 0,
        result as int == count_segments(s@) - 1,
        result as int <= s.len() - 1,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed `i` and `segments` initialization, and updated invariants conditions to avoid out-of-bounds access. The invariant was updated for the `segments` variable in the outer loop, and `start_segment_idx` for the inner loop. */
    let n = s.len();
    if n == 0 {
        return 0i8;
    }

    let mut segments: int = 0;
    let mut i: int = 0;

    while i < n
        invariant
            0 <= i <= n,
            segments >= 0,
            segments == count_segments(s@.subrange(0, i as int)),
        decreases n - i
    {
        let current_char = s[i as int];
        segments = segments + 1;
        let start_segment_idx = i;
        
        while i < n && s[i as int] == current_char
            invariant
                0 <= start_segment_idx <= i <= n,
                segments == (
                    if start_segment_idx == 0 {
                        1
                    } else {
                        count_segments(s@.subrange(0, start_segment_idx as int)) + 1
                    }
                ),
                forall|j: int| start_segment_idx <= j < i ==> s[j as int] == current_char,
            decreases n - i
        {
            i = i + 1;
        }
    }
    
    (segments - 1) as i8
}
// </vc-code>


}

fn main() {}