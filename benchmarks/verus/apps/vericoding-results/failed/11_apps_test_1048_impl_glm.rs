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
/* helper modified by LLM (iteration 3): fixed while loop invariant block structure */
fn count_commands(commands: &Vec<char>) -> (usize, usize, usize, usize)
    ensures 
        result.0 == count_char(commands@, 'L'),
        result.1 == count_char(commands@, 'R'),
        result.2 == count_char(commands@, 'U'),
        result.3 == count_char(commands@, 'D'),
{
    let mut i = 0;
    let mut countL = 0;
    let mut countR = 0;
    let mut countU = 0;
    let mut countD = 0;
    while i < commands.len()
        invariant
            0 <= i <= commands.len(),
            countL == count_char(commands@.subrange(0, i as int), 'L'),
            countR == count_char(commands@.subrange(0, i as int), 'R'),
            countU == count_char(commands@.subrange(0, i as int), 'U'),
            countD == count_char(commands@.subrange(0, i as int), 'D'),
    {
        match commands[i] {
            'L' => countL += 1,
            'R' => countR += 1,
            'U' => countU += 1,
            'D' => countD += 1,
            _ => {},
        }
        i += 1;
    }
    (countL, countR, countU, countD)
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
    /* code modified by LLM (iteration 3): no changes needed */
    let (countL, countR, countU, countD) = count_commands(&commands);
    let minLR = if countL < countR { countL } else { countR };
    let minUD = if countU < countD { countU } else { countD };
    let result = 2 * minLR + 2 * minUD;
    result
}
// </vc-code>


}

fn main() {}