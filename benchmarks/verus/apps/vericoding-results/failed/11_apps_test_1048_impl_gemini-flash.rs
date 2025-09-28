// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn count_char(s: Seq<char>, c: char) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0int
    } else {
        (if s[0] == c { 1int } else { 0int }) + count_char(s.subrange(1, s.len() as int), c)
    }
}

spec fn min(a: int, b: int) -> int {
    if a <= b { a } else { b }
}

spec fn valid_commands(commands: Seq<char>) -> bool {
    forall|i: int| 0 <= i < commands.len() ==> commands[i] == 'L' || commands[i] == 'R' || commands[i] == 'U' || commands[i] == 'D'
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fix `int` literal inference by adding `int` suffix to 0. */
spec fn count_char_prefix(s: Seq<char>, len: int, c: char) -> int
    requires 0 <= len <= s.len()
    decreases len
{
    if len == 0 {
        0 int
    } else {
        (if s[len - 1] == c { 1 int } else { 0 int }) + count_char_prefix(s, len - 1, c)
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: usize, commands: Vec<char>) -> (result: usize)
    requires 
        n >= 0,
        commands@.len() == n,
        valid_commands(commands@)
    ensures 
        result >= 0,
        result <= n,
        result % 2 == 0,
        result as int == 2 * min(count_char(commands@, 'L'), count_char(commands@, 'R')) + 
                         2 * min(count_char(commands@, 'U'), count_char(commands@, 'D'))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected `proof` block to refer to `commands@[i]`, ensuring `count_char` accurately reflects the update. */
{
    let mut l_count: int = 0;
    let mut r_count: int = 0;
    let mut u_count: int = 0;
    let mut d_count: int = 0;

    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i as int <= n as int,
            commands@.len() == n,
            valid_commands(commands@),
            l_count == count_char(commands@.subrange(0, i as int), 'L'),
            r_count == count_char(commands@.subrange(0, i as int), 'R'),
            u_count == count_char(commands@.subrange(0, i as int), 'U'),
            d_count == count_char(commands@.subrange(0, i as int), 'D'),
    {
        proof {
            if i < n {
                let current_char = commands@[i as int];
                assert(count_char(commands@.subrange(0, i as int + 1), current_char) == count_char(commands@.subrange(0, i as int), current_char) + (if commands@[i as int] == current_char { 1 } else { 0 }));
            }
        }

        let command = commands[i];
        if command == 'L' {
            l_count = l_count + 1;
        } else if command == 'R' {
            r_count = r_count + 1;
        } else if command == 'U' {
            u_count = u_count + 1;
        } else if command == 'D' {
            d_count = d_count + 1;
        }
        i = i + 1;
    }

    proof {
        assert(l_count == count_char(commands@, 'L'));
        assert(r_count == count_char(commands@, 'R'));
        assert(u_count == count_char(commands@, 'U'));
        assert(d_count == count_char(commands@, 'D'));
    }

    let horizontal_pairs = min(l_count, r_count);
    let vertical_pairs = min(u_count, d_count);

    let total_pairs = 2 * (horizontal_pairs + vertical_pairs);
    total_pairs as usize
}
// </vc-code>


}

fn main() {}