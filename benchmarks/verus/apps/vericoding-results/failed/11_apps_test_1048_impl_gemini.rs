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
proof fn lemma_count_char_concat(s1: Seq<char>, s2: Seq<char>, c: char)
    ensures
        count_char(s1 + s2, c) == count_char(s1, c) + count_char(s2, c),
    decreases s1.len()
{
    if s1.len() > 0 {
        let s1_rest = s1.subrange(1, s1.len() as int);
        assert((s1 + s2).subrange(1, (s1 + s2).len() as int) == s1_rest + s2);
        lemma_count_char_concat(s1_rest, s2, c);
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
{
    /* code modified by LLM (iteration 2): [fix compilation error: Seq::one -> seq!] */
    let mut count_l: usize = 0;
    let mut count_r: usize = 0;
    let mut count_u: usize = 0;
    let mut count_d: usize = 0;
    let mut i: usize = 0;
    while i < n 
        invariant
            0 <= i <= n,
            i == count_l + count_r + count_u + count_d,
            count_l as int == count_char(commands@.subrange(0, i as int), 'L'),
            count_r as int == count_char(commands@.subrange(0, i as int), 'R'),
            count_u as int == count_char(commands@.subrange(0, i as int), 'U'),
            count_d as int == count_char(commands@.subrange(0, i as int), 'D'),
        decreases n - i
    {
        let cmd = commands[i];
        proof {
            let s_i = commands@.subrange(0, i as int);
            let s_one = seq![cmd];
            assert(commands@.subrange(0, i as int + 1) == s_i + s_one);
            lemma_count_char_concat(s_i, s_one, 'L');
            lemma_count_char_concat(s_i, s_one, 'R');
            lemma_count_char_concat(s_i, s_one, 'U');
            lemma_count_char_concat(s_i, s_one, 'D');
        }

        if cmd == 'L' {
            count_l = count_l + 1;
        } else if cmd == 'R' {
            count_r = count_r + 1;
        } else if cmd == 'U' {
            count_u = count_u + 1;
        } else {
            count_d = count_d + 1;
        }
        i = i + 1;
    }

    let min_lr = if count_l <= count_r { count_l } else { count_r };
    let min_ud = if count_u <= count_d { count_u } else { count_d };

    2 * min_lr + 2 * min_ud
}
// </vc-code>


}

fn main() {}