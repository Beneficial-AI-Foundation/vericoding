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
/* helper modified by LLM (iteration 5): Added lemmas to connect index-based existence to subrange contains */
proof fn lemma_subrange_contains(s: Seq<char>, start: int, end: int, c: char)
    requires
        0 <= start < end,
        end <= s.len(),
        exists|k: int| start <= k < end && s[k] == c
    ensures
        s.subrange(start, end).contains(c)
{
    let k = choose|k: int| start <= k < end && s[k] == c;
    assert(s.subrange(start, end)[k - start] == s[k]);
    assert(s.subrange(start, end).contains(c));
}

proof fn lemma_no_has_all_three_colors(s: Seq<char>, i: int)
    requires
        0 <= i <= s.len() - 3,
        !(exists|k: int| i <= k < i + 3 && s[k] == 'A') ||
        !(exists|k: int| i <= k < i + 3 && s[k] == 'B') ||
        !(exists|k: int| i <= k < i + 3 && s[k] == 'C')
    ensures
        !has_all_three_colors(s, i)
{
    if !(exists|k: int| i <= k < i + 3 && s[k] == 'A') {
        assert(!s.subrange(i, i + 3).contains('A'));
    } else if !(exists|k: int| i <= k < i + 3 && s[k] == 'B') {
        assert(!s.subrange(i, i + 3).contains('B'));
    } else {
        assert(!s.subrange(i, i + 3).contains('C'));
    }
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
    /* code modified by LLM (iteration 5): Added proof blocks with helper lemmas for subrange contains */
    if s.len() < 3 {
        return vec!['N', 'o'];
    }
    
    let mut i: usize = 0;
    while i <= s.len() - 3
        invariant
            i <= s.len(),
            s.len() >= 3,
            i <= s.len() - 3 || i == s.len() - 2 || i == s.len() - 1 || i == s.len(),
            forall|j: int| 0 <= j < i as int ==> !has_all_three_colors(s@, j)
        decreases s.len() - i
    {
        let mut has_a = false;
        let mut has_b = false;
        let mut has_c = false;
        
        let mut j: usize = i;
        while j < i + 3
            invariant
                i <= j,
                j <= i + 3,
                i <= s.len() - 3,
                j <= s.len(),
                has_a ==> exists|k: int| i as int <= k < j as int && s@[k] == 'A',
                has_b ==> exists|k: int| i as int <= k < j as int && s@[k] == 'B',
                has_c ==> exists|k: int| i as int <= k < j as int && s@[k] == 'C',
                !has_a ==> forall|k: int| i as int <= k < j as int ==> s@[k] != 'A',
                !has_b ==> forall|k: int| i as int <= k < j as int ==> s@[k] != 'B',
                !has_c ==> forall|k: int| i as int <= k < j as int ==> s@[k] != 'C'
            decreases i + 3 - j
        {
            if s[j] == 'A' {
                has_a = true;
            } else if s[j] == 'B' {
                has_b = true;
            } else if s[j] == 'C' {
                has_c = true;
            }
            j = j + 1;
        }
        
        if has_a && has_b && has_c {
            proof {
                assert(exists|k: int| i as int <= k < i as int + 3 && s@[k] == 'A');
                assert(exists|k: int| i as int <= k < i as int + 3 && s@[k] == 'B');
                assert(exists|k: int| i as int <= k < i as int + 3 && s@[k] == 'C');
                lemma_subrange_contains(s@, i as int, i as int + 3, 'A');
                lemma_subrange_contains(s@, i as int, i as int + 3, 'B');
                lemma_subrange_contains(s@, i as int, i as int + 3, 'C');
                assert(s@.subrange(i as int, i as int + 3).contains('A'));
                assert(s@.subrange(i as int, i as int + 3).contains('B'));
                assert(s@.subrange(i as int, i as int + 3).contains('C'));
                assert(has_all_three_colors(s@, i as int));
                assert(possible_to_get_all_colors(s@));
            }
            return vec!['Y', 'e', 's'];
        }
        
        proof {
            if !has_a || !has_b || !has_c {
                lemma_no_has_all_three_colors(s@, i as int);
            }
        }
        
        if i == s.len() - 3 {
            break;
        }
        i = i + 1;
    }
    
    proof {
        assert(i >= s.len() - 3);
        assert(forall|k: int| 0 <= k < i as int ==> !has_all_three_colors(s@, k));
        if s.len() >= 3 {
            assert(i as int >= s@.len() - 3);
            assert(forall|k: int| 0 <= k <= s@.len() - 3 ==> !has_all_three_colors(s@, k));
        }
        assert(!possible_to_get_all_colors(s@));
    }
    vec!['N', 'o']
}
// </vc-code>


}

fn main() {}