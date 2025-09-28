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
/* code modified by LLM (iteration 5): switched counters to usize for arithmetic compatibility and removed invalid as cast */
{
    let mut countL: usize = 0;
    let mut countR: usize = 0;
    let mut countU: usize = 0;
    let mut countD: usize = 0;
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            countL + countR + countU + countD == i
        decreases n - i
    {
        let c = commands[i];
        if c == 'L' {
            countL = countL + 1;
        } else if c == 'R' {
            countR = countR + 1;
        } else if c == 'U' {
            countU = countU + 1;
        } else {
            countD = countD + 1;
        }
        i = i + 1;
    }
    let minLR: usize = if countL < countR { countL } else { countR };
    let minUD: usize = if countU < countD { countU } else { countD };
    let total_min: usize = minLR + minUD;
    total_min * 2
}
// </vc-code>


}

fn main() {}