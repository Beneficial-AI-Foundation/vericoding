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
/* helper modified by LLM (iteration 5): added proof that demonstrates has_all_three_colors when A, B, C found */
spec fn contains_char(s: Seq<char>, c: char) -> bool {
    exists|i: int| 0 <= i < s.len() && s[i] == c
}

proof fn lemma_subrange_contains(s: Seq<char>, start: int, end: int, c: char)
    requires
        0 <= start <= end <= s.len(),
        contains_char(s.subrange(start, end), c)
    ensures
        exists|i: int| start <= i < end && s[i] == c
{
}

proof fn lemma_has_all_three_colors_equiv(s: Seq<char>, start: int)
    requires
        0 <= start <= s.len() - 3
    ensures
        has_all_three_colors(s, start) == (
            contains_char(s.subrange(start, start + 3), 'A') &&
            contains_char(s.subrange(start, start + 3), 'B') &&
            contains_char(s.subrange(start, start + 3), 'C')
        )
{
}

proof fn lemma_found_all_colors_implies_has_all_three(s: Seq<char>, start: int)
    requires
        0 <= start <= s.len() - 3,
        exists|k: int| start <= k < start + 3 && s[k] == 'A',
        exists|k: int| start <= k < start + 3 && s[k] == 'B',
        exists|k: int| start <= k < start + 3 && s[k] == 'C'
    ensures
        has_all_three_colors(s, start)
{
    assert(s.subrange(start, start + 3).contains('A'));
    assert(s.subrange(start, start + 3).contains('B'));
    assert(s.subrange(start, start + 3).contains('C'));
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
/* code modified by LLM (iteration 5): added proof block to establish has_all_three_colors when returning Yes */
{
    if s.len() < 3 {
        return vec!['N', 'o'];
    }
    
    let mut i: usize = 0;
    while i <= s.len() - 3
        invariant
            0 <= i <= s.len() - 3 + 1,
            s@.len() >= 3,
            forall|j: int| 0 <= j < i ==> !has_all_three_colors(s@, j)
        decreases s.len() - 3 - i + 1
    {
        let mut has_a = false;
        let mut has_b = false;
        let mut has_c = false;
        
        let mut j: usize = 0;
        while j < 3
            invariant
                0 <= j <= 3,
                i + 3 <= s.len(),
                has_a == exists|k: int| i <= k < i + j && s@[k] == 'A',
                has_b == exists|k: int| i <= k < i + j && s@[k] == 'B',
                has_c == exists|k: int| i <= k < i + j && s@[k] == 'C'
            decreases 3 - j
        {
            if s[i + j] == 'A' {
                has_a = true;
            } else if s[i + j] == 'B' {
                has_b = true;
            } else if s[i + j] == 'C' {
                has_c = true;
            }
            j += 1;
        }
        
        if has_a && has_b && has_c {
            proof {
                assert(exists|k: int| i <= k < i + 3 && s@[k] == 'A');
                assert(exists|k: int| i <= k < i + 3 && s@[k] == 'B');
                assert(exists|k: int| i <= k < i + 3 && s@[k] == 'C');
                lemma_found_all_colors_implies_has_all_three(s@, i as int);
                assert(has_all_three_colors(s@, i as int));
                assert(possible_to_get_all_colors(s@));
            }
            return vec!['Y', 'e', 's'];
        }
        
        i += 1;
    }
    
    vec!['N', 'o']
}
// </vc-code>


}

fn main() {}