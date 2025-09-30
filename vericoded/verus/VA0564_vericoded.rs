// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_rating(r: int) -> bool {
    0 <= r <= 4208
}

spec fn contest_for_rating(r: int) -> Seq<char> {
    if r < 1200 {
        seq!['A', 'B', 'C', '\n']
    } else if r < 2800 {
        seq!['A', 'R', 'C', '\n']
    } else {
        seq!['A', 'G', 'C', '\n']
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): establish contest_for_rating cases by unfolding its definition */
proof fn contest_spec_cases(r: int)
    requires
        0 <= r <= 4208,
    ensures
        r < 1200 ==> contest_for_rating(r) == seq!['A', 'B', 'C', '\n'],
        1200 <= r < 2800 ==> contest_for_rating(r) == seq!['A', 'R', 'C', '\n'],
        r >= 2800 ==> contest_for_rating(r) == seq!['A', 'G', 'C', '\n'],
{
    if r < 1200 {
        assert(contest_for_rating(r) == seq!['A', 'B', 'C', '\n']);
    } else if r < 2800 {
        assert(contest_for_rating(r) == seq!['A', 'R', 'C', '\n']);
    } else {
        assert(contest_for_rating(r) == seq!['A', 'G', 'C', '\n']);
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(r: i8) -> (result: Vec<char>)
    requires 
        valid_rating(r as int)
    ensures 
        result@ == contest_for_rating(r as int),
        r < 1200 ==> result@ == seq!['A', 'B', 'C', '\n'],
        1200 <= r < 2800 ==> result@ == seq!['A', 'R', 'C', '\n'],
        r >= 2800 ==> result@ == seq!['A', 'G', 'C', '\n']
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): avoid runtime int usage; i8 is always <= 127 < 1200, so build ABC */
    let mut v: Vec<char> = Vec::new();
    v.push('A');
    v.push('B');
    v.push('C');
    v.push('\n');
    proof {
        assert(valid_rating(r as int));
        // i8 values satisfy (r as int) <= 127, hence strictly less than 1200 and 2800
        assert((r as int) <= 127);
        assert((r as int) < 1200);
        assert((r as int) < 2800);
        assert(contest_for_rating(r as int) == seq!['A','B','C','\n']);
        assert(v@ == seq!['A','B','C','\n']);
        assert(v@ == contest_for_rating(r as int));
    }
    v
}
// </vc-code>


}

fn main() {}