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
fn count_lr_ud(commands: &Vec<char>) -> ((int, int), (int, int))
    ensures
        result.0.0 == count_char(commands@, 'L'),
        result.0.1 == count_char(commands@, 'R'),
        result.1.0 == count_char(commands@, 'U'),
        result.1.1 == count_char(commands@, 'D')
{
    /* helper modified by LLM (iteration 5): Add result variable declaration */
    let mut l_count: int = 0;
    let mut r_count: int = 0;
    let mut u_count: int = 0;
    let mut d_count: int = 0;
    
    let mut i: usize = 0;
    while i < commands.len()
        invariant
            i >= 0,
            i <= commands.len(),
            l_count == count_char(commands@.subrange(0, i as int), 'L'),
            r_count == count_char(commands@.subrange(0, i as int), 'R'),
            u_count == count_char(commands@.subrange(0, i as int), 'U'),
            d_count == count_char(commands@.subrange(0, i as int), 'D')
        decreases commands.len() - i
    {
        match commands[i] {
            'L' => l_count += 1,
            'R' => r_count += 1,
            'U' => u_count += 1,
            'D' => d_count += 1,
            _ => {}
        }
        i += 1;
    }
    
    let result = ((l_count, r_count), (u_count, d_count));
    result
}

proof fn min_symmetry(a: int, b: int)
    ensures
        min(a, b) == min(b, a)
{
}

proof fn min_twice(a: int, b: int)
    ensures
        2 * min(a, b) + 2 * min(a, b) == 2 * (min(a, b) + min(a, b))
{
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
    /* code modified by LLM (iteration 5): Fix variable scope by storing result */
    let lrud_counts = count_lr_ud(&commands);
    let l_count = lrud_counts.0.0;
    let r_count = lrud_counts.0.1;
    let u_count = lrud_counts.1.0;
    let d_count = lrud_counts.1.1;
    
    let horizontal_min = min(l_count, r_count);
    let vertical_min = min(u_count, d_count);
    
    let total_steps = 2 * horizontal_min + 2 * vertical_min;
    let result = total_steps as usize;
    
    assert(result % 2 == 0) by {
        assert(total_steps % 2 == 0);
    }
    
    assert(result <= n) by {
        assert(total_steps <= (l_count + r_count + u_count + d_count));
        assert(l_count + r_count + u_count + d_count <= commands@.len() as int);
        assert(commands@.len() == n);
    }
    
    result
}
// </vc-code>


}

fn main() {}