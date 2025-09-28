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

proof fn lemma_initial_condition_valid(s: Seq<char>)
    requires
        s.len() >= 3,
        valid_input(s)
    ensures
        exists|i: int| 0 <= i <= s.len() - 3 && has_all_three_colors(s, i) ==> possible_to_get_all_colors(s)
{
    /* helper modified by LLM (iteration 5): Refined lemma to handle empty case and bounds */
    assert(possible_to_get_all_colors(s) == (s.len() >= 3 && exists|i: int| 0 <= i <= s.len() - 3 && has_all_three_colors(s, i)));
    if exists|i: int| 0 <= i <= s.len() - 3 && has_all_three_colors(s, i) {
        assert(possible_to_get_all_colors(s));
    }
}

proof fn lemma_has_all_three_colors_implies_possible(s: Seq<char>, start: int)
    requires
        0 <= start <= s.len() - 3,
        has_all_three_colors(s, start)
    ensures
        possible_to_get_all_colors(s)
{
    assert(s.len() >= 3);
    assert(exists|i: int| 0 <= i <= s.len() - 3 && has_all_three_colors(s, i));
    assert(possible_to_get_all_colors(s));
}

spec fn found_sequence_at_position(s: &[char], index: int) -> bool
    recommends 0 <= index <= s@.len() - 3
{
    has_all_three_colors(s@, index)
}

proof fn lemma_while_invariant_maintains_bounds(len: int, index: usize)
    requires
        len >= 3,
        index as int >= 0,
        index <= len - 3
    ensures
        index as int + 2 < len
{
    assert(index + 2 < len);
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
{
    /* code modified by LLM (iteration 5): Fixed bounds checking, loop invariant and arithmetic */
    if s.len() < 3 {
        return vec!['N', 'o'];
    }
    
    let len = s.len();
    let mut index: usize = 0;
    
    while index <= len - 3
        invariant
            index <= len,
            forall|i: int| 0 <= i < index as int ==> !found_sequence_at_position(s, i)
        decreases
            if index <= len - 3 { len - index } else { 0 }
    {
        lemma_while_invariant_maintains_bounds(len, index);
        assert(index + 2 < len);
        
        let has_a = s[index] == 'A' || s[index + 1] == 'A' || s[index + 2] == 'A';
        let has_b = s[index] == 'B' || s[index + 1] == 'B' || s[index + 2] == 'B';
        let has_c = s[index] == 'C' || s[index + 1] == 'C' || s[index + 2] == 'C';
        
        if has_a && has_b && has_c {
            proof {
                lemma_has_all_three_colors_implies_possible(s@, index as int);
            }
            return vec!['Y', 'e', 's'];
        }
        
        index += 1;
    }
    
    vec!['N', 'o']
}
// </vc-code>


}

fn main() {}