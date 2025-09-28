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

/* helper modified by LLM (iteration 5): No helpers needed as logic is in code */


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
{
    /* code modified by LLM (iteration 5): Fixed compilation errors by moving ghost variable to proof block, added assertions for invariants and post-conditions */
    let n: usize = s.len();
    if n < 3 {
        return vec!['N', 'o'];
    }
    let mut i: usize = 0;
    while i <= n - 3
        invariant
            0 <= i <= n - 3,
            forall|j: int| 0 <= j < i ==> !has_all_three_colors(s@, j),
        decreases n - i
    {
        if (s[i] == 'A' || s[i + 1] == 'A' || s[i + 2] == 'A') &&
           (s[i] == 'B' || s[i + 1] == 'B' || s[i + 2] == 'B') &&
           (s[i] == 'C' || s[i + 1] == 'C' || s[i + 2] == 'C') {
            proof {
                assert(has_all_three_colors(s@, i));
            }
            return vec!['Y', 'e', 's'];
        }
        proof {
            assert(!has_all_three_colors(s@, i));
        }
        i = i + 1;
    }
    return vec!['N', 'o'];
}
// </vc-code>


}

fn main() {}