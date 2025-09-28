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
fn exec_has_all_three_colors(sub: &[char]) -> (result: bool)
    requires
        sub@.len() == 3,
        valid_input(sub@),
    ensures
        result == has_all_three_colors(sub@, 0),
{
    let has_a = sub[0] == 'A' || sub[1] == 'A' || sub[2] == 'A';
    let has_b = sub[0] == 'B' || sub[1] == 'B' || sub[2] == 'B';
    let has_c = sub[0] == 'C' || sub[1] == 'C' || sub[2] == 'C';

    proof {
        assert(sub@.contains('A') <==> has_a);
        assert(sub@.contains('B') <==> has_b);
        assert(sub@.contains('C') <==> has_c);
    }

    has_a && has_b && has_c
}

/* helper modified by LLM (iteration 5): [no change, just updating iteration count] */
proof fn lemma_has_all_three_colors_subrange(s: Seq<char>, i: int)
    requires
        0 <= i <= s.len() - 3,
    ensures
        has_all_three_colors(s, i) == has_all_three_colors(s.subrange(i, i + 3), 0),
{
    let sub = s.subrange(i, i + 3);
    assert(sub.len() == 3);
    assert(sub.subrange(0, 3) =~= sub);
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
    /* code modified by LLM (iteration 5): [used s.subslice to fix compilation error] */
    if s.len() < 3 {
        proof {
            assert(!possible_to_get_all_colors(s@));
        }
        return vec!['N', 'o'];
    }

    let mut i: usize = 0;
    while i + 3 <= s.len()
        invariant
            s.len() >= 3,
            0 <= i <= s.len() - 2,
            valid_input(s@),
            forall|k: int| 0 <= k < i as int ==> !has_all_three_colors(s@, k)
        decreases s.len() - i
    {
        let sub = s.subslice(i, i + 3);
        if exec_has_all_three_colors(sub) {
            proof {
                lemma_has_all_three_colors_subrange(s@, i as int);
                assert(has_all_three_colors(s@, i as int));
                assert(possible_to_get_all_colors(s@));
            }
            return vec!['Y', 'e', 's'];
        }
        i = i + 1;
    }

    proof {
        assert(forall|k: int| 0 <= k <= s@.len() - 3 ==> !has_all_three_colors(s@, k));
        assert(!possible_to_get_all_colors(s@));
    }
    vec!['N', 'o']
}
// </vc-code>


}

fn main() {}