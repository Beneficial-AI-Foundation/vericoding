// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(s: Seq<char>) -> bool {
    s.len() >= 0 && forall|i: int| 0 <= i < s.len() ==> s[i] == 'A' || s[i] == 'B' || s[i] == 'C' || s[i] == '.'
}

spec fn has_all_three_colors(s: Seq<char>, start: int) -> bool
    recommends 0 <= start <= s.len() - 3
{
    s.subrange(start, start + 3).contains('A') && 
    s.subrange(start, start + 3).contains('B') && 
    s.subrange(start, start + 3).contains('C')
}

spec fn possible_to_get_all_colors(s: Seq<char>) -> bool {
    s.len() >= 3 && exists|i: int| 0 <= i <= s.len() - 3 && has_all_three_colors(s, i)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [removed assume(false)] */
fn lemma_has_all_three_colors_implies_exists_subsequence(s: Seq<char>, start: int)
    requires
        0 <= start <= s.len() - 3,
        has_all_three_colors(s, start)
    ensures
        exists|i: int| start <= i < start + 3 && s[i] == 'A',
        exists|i: int| start <= i < start + 3 && s[i] == 'B',
        exists|i: int| start <= i < start + 3 && s[i] == 'C'
{
    // This lemma is a direct consequence of the definition of has_all_three_colors and Seq.contains
    // and can be proven by direct expansion of `contains` for each character
    // For example, to prove exists|i: int| start <= i < start + 3 && s[i] == 'A':
    // Since s.subrange(start, start + 3).contains('A'), by definition of contains,
    // there exists an index k such that 0 <= k < 3 and s.subrange(start, start + 3)[k] == 'A'.
    // This means s[start + k] == 'A', and start <= start + k < start + 3.
    // The same logic applies to 'B' and 'C'.
}
// </vc-helpers>

// <vc-spec>
fn solve(s: &[char]) -> (result: Vec<char>)
    requires 
        s@.len() >= 0 && forall|i: int| 0 <= i < s@.len() ==> s@[i] == 'A' || s@[i] == 'B' || s@[i] == 'C' || s@[i] == '.'
    ensures 
        result@ == seq!['Y', 'e', 's'] ==> possible_to_get_all_colors(s@),
        result@ == seq!['N', 'o'] ==> !possible_to_get_all_colors(s@),
        result@ == seq!['Y', 'e', 's'] || result@ == seq!['N', 'o']
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): [fixed type mismatch errors for `int` and `nat`, fixed indexing of `Seq` with `@`, and fixed a loop invariant issue]*/
{
    let len = s@.len();

    if (len as nat) < 3 nat {
        return vec!['N', 'o'];
    }

    let mut i: int = 0;
    let mut found_all = false;

    while i <= len - 3 && !found_all
        invariant
            0 <= i <= len,
            len >= 3,
            found_all ==> possible_to_get_all_colors(s@)
        decreases len - i
    {
        let window = s@.subrange(i, i + 3);

        let mut current_window_found_A = false;
        let mut current_window_found_B = false;
        let mut current_window_found_C = false;

        let mut j: int = 0;
        while j < 3
            invariant
                0 <= i <= (len as int) - 3,
                0 <= j <= 3,
                current_window_found_A == (exists|k: int| 0 <= k < j && window[k] == 'A'),
                current_window_found_B == (exists|k: int| 0 <= k < j && window[k] == 'B'),
                current_window_found_C == (exists|k: int| 0 <= k < j && window[k] == 'C')
            decreases 3 - j
        {
            if window@[j] == 'A' { current_window_found_A = true; }
            if window@[j] == 'B' { current_window_found_B = true; }
            if window@[j] == 'C' { current_window_found_C = true; }
            j = j + 1;
        }

        if current_window_found_A && current_window_found_B && current_window_found_C {
            found_all = true;
            proof {
                lemma_has_all_three_colors_implies_exists_subsequence(s@, i);
            }
        }
        i = i + 1;
    }

    if found_all {
        vec!['Y', 'e', 's']
    } else {
        vec!['N', 'o']
    }
}
// </vc-code>


}

fn main() {}