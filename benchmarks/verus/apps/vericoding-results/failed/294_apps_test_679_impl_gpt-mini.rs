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
/* helper modified by LLM (iteration 5): boolean spec checking three-char window via direct indexing */
spec fn window_contains_all(s: Seq<char>, start: int) -> bool
    recommends 0 <= start <= s.len() - 3
{
    let a = s[start];
    let b = s[start + 1];
    let c = s[start + 2];
    (a == 'A' || b == 'A' || c == 'A') &&
    (a == 'B' || b == 'B' || c == 'B') &&
    (a == 'C' || b == 'C' || c == 'C')
}

/* helper modified by LLM (iteration 5): lemma proving equivalence between window_contains_all and has_all_three_colors */
fn window_equiv_has_all(s: Seq<char>, start: int) -> (res: ())
    requires 0 <= start <= s.len() - 3,
    ensures has_all_three_colors(s, start) == window_contains_all(s, start),
{
    proof {
        assert(s.subrange(start, start + 3).contains('A') == (s[start] == 'A' || s[start + 1] == 'A' || s[start + 2] == 'A'));
        assert(s.subrange(start, start + 3).contains('B') == (s[start] == 'B' || s[start + 1] == 'B' || s[start + 2] == 'B'));
        assert(s.subrange(start, start + 3).contains('C') == (s[start] == 'C' || s[start + 1] == 'C' || s[start + 2] == 'C'));
        assert(has_all_three_colors(s, start) == window_contains_all(s, start));
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
    /* code modified by LLM (iteration 5): scan windows and relate runtime chars to spec via proofs to conclude existence */
    let n: usize = s.len();
    if n < 3 {
        return vec!['N', 'o'];
    }

    let mut i: usize = 0usize;
    let mut found: bool = false;
    while i <= n - 3
        invariant
            i <= n,
            found == exists|j: int| 0 <= j <= (i as int) && has_all_three_colors(s@, j),
        decreases n - i
    {
        let a = s[i];
        let b = s[i + 1];
        let c = s[i + 2];
        if (a == 'A' || b == 'A' || c == 'A') && (a == 'B' || b == 'B' || c == 'B') && (a == 'C' || b == 'C' || c == 'C') {
            proof {
                assert(0 <= i as int && i as int <= s@.len() - 3);
                assert(s@[i as int] == a);
                assert(s@[i as int + 1] == b);
                assert(s@[i as int + 2] == c);
                assert(s@[i as int] == 'A' || s@[i as int + 1] == 'A' || s@[i as int + 2] == 'A');
                assert(s@[i as int] == 'B' || s@[i as int + 1] == 'B' || s@[i as int + 2] == 'B');
                assert(s@[i as int] == 'C' || s@[i as int + 1] == 'C' || s@[i as int + 2] == 'C');
                assert(window_contains_all(s@, i as int));
                window_equiv_has_all(s@, i as int);
                assert(has_all_three_colors(s@, i as int));
            }
            found = true;
            break;
        } else {
            i = i + 1;
        }
    }

    if found {
        proof {
            assert(found == exists|j: int| 0 <= j <= (i as int) && has_all_three_colors(s@, j));
            let j: int = choose|j: int| 0 <= j <= (i as int) && has_all_three_colors(s@, j);
            assert(0 <= j && j <= i as int);
            assert(i as int <= s@.len() - 3);
            assert(j <= s@.len() - 3);
            assert(s@.len() >= 3);
            assert(possible_to_get_all_colors(s@));
        }
        vec!['Y', 'e', 's']
    } else {
        vec!['N', 'o']
    }
}

// </vc-code>


}

fn main() {}