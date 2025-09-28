// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(s: Seq<char>) -> bool {
    s.len() >= 3
}

spec fn count_excessive_positions(s: Seq<char>) -> int {
    count_excessive_positions_helper(s, 0, 0)
}

spec fn count_excessive_positions_helper(s: Seq<char>, pos: int, consecutive_x: int) -> int
    decreases s.len() - pos
{
    if pos >= s.len() {
        0
    } else {
        let new_consecutive_x = if s[pos] == 'x' { consecutive_x + 1 } else { 0 };
        let current_contribution: int = if new_consecutive_x > 2 { 1 } else { 0 };
        current_contribution + count_excessive_positions_helper(s, pos + 1, new_consecutive_x)
    }
}

spec fn consecutive_x_count(s: Seq<char>, pos: int) -> int
    decreases pos
{
    if pos == 0 {
        0
    } else if pos > 0 && pos <= s.len() && s[pos - 1] == 'x' {
        1 + consecutive_x_count(s, pos - 1)
    } else {
        0
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): step lemma with explicit int literals to avoid type ambiguity */
proof fn lemma_step(s: Seq<char>, pos: int, consecutive_x: int, acc: int)
    requires
        0 <= pos,
        pos < s.len() as int,
        acc + count_excessive_positions_helper(s, pos, consecutive_x) == count_excessive_positions(s),
    ensures
        acc + ((if s[pos] == 'x' { if consecutive_x + 1 > 2 { 1 as int } else { 0 as int } } else { 0 as int }) + count_excessive_positions_helper(s, pos + 1, if s[pos] == 'x' { consecutive_x + 1 } else { 0 })) == count_excessive_positions(s),
    decreases
        (s.len() as int) - pos
{
    proof {
        assert(count_excessive_positions_helper(s, pos, consecutive_x)
            == ((if s[pos] == 'x' { if consecutive_x + 1 > 2 { 1 as int } else { 0 as int } } else { 0 as int }) + count_excessive_positions_helper(s, pos + 1, if s[pos] == 'x' { consecutive_x + 1 } else { 0 })));
        assert(acc + ((if s[pos] == 'x' { if consecutive_x + 1 > 2 { 1 as int } else { 0 as int } } else { 0 as int }) + count_excessive_positions_helper(s, pos + 1, if s[pos] == 'x' { consecutive_x + 1 } else { 0 }))) == count_excessive_positions(s));
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: i8)
    requires valid_input(s@)
    ensures 
        result >= 0,
        result as int <= s@.len(),
        result as int == count_excessive_positions(s@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterative computation with invariant and lemma_step call */
    let len_r = s.len();
    let mut i: usize = 0;
    let mut consecutive: usize = 0;
    let mut acc: usize = 0;

    while i < len_r
        invariant
            0 <= i as int && i as int <= len_r as int,
            0 <= acc as int && acc as int <= len_r as int,
            0 <= consecutive as int && consecutive as int <= i as int,
            acc as int + count_excessive_positions_helper(s@, i as int, consecutive as int) == count_excessive_positions(s@),
        decreases
            (len_r as int) - i as int
    {
        let old_i = i;
        let old_consecutive = consecutive;
        let old_acc = acc;

        let c = if s[old_i] == 'x' { old_consecutive + 1 } else { 0 };
        let contrib = if c > 2 { 1 } else { 0 };

        proof {
            lemma_step(s@, old_i as int, old_consecutive as int, old_acc as int);
        }

        acc = old_acc + contrib;
        consecutive = c;
        i = old_i + 1;
    }

    let result = acc as i8;
    result
}

// </vc-code>


}

fn main() {}