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
/* helper modified by LLM (iteration 5): fixed invariant and added precondition */
proof fn count_char_properties(s: Seq<char>, c: char)
    ensures count_char(s, c) >= 0
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        count_char_properties(s.subrange(1, s.len() as int), c);
    }
}

proof fn count_char_bounded(s: Seq<char>, c: char)
    ensures count_char(s, c) <= s.len()
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        count_char_bounded(s.subrange(1, s.len() as int), c);
    }
}

proof fn min_properties(a: int, b: int)
    ensures min(a, b) <= a,
            min(a, b) <= b,
            min(a, b) == a || min(a, b) == b
{
}

proof fn count_char_subrange_property(s: Seq<char>, c: char, i: int)
    requires 0 <= i < s.len()
    ensures count_char(s.subrange(0, i + 1), c) == count_char(s.subrange(0, i), c) + (if s[i] == c { 1 } else { 0 })
{
    if i == 0 {
        assert(s.subrange(0, 1) =~= seq![s[0]]);
        assert(s.subrange(0, 0) =~= seq![]);
    } else {
        count_char_subrange_property(s, c, i - 1);
    }
}

fn count_char_imperative(commands: &Vec<char>, target: char) -> (count: usize)
    requires valid_commands(commands@),
             commands.len() < usize::MAX
    ensures count as int == count_char(commands@, target)
{
    let mut count = 0;
    let mut i = 0;
    
    while i < commands.len()
        invariant
            0 <= i <= commands.len(),
            count as int == count_char(commands@.subrange(0, i as int), target),
            count <= i
        decreases commands.len() - i
    {
        proof {
            count_char_subrange_property(commands@, target, i as int);
        }
        
        if commands[i] == target {
            count = count + 1;
        }
        i = i + 1;
    }
    
    proof {
        assert(commands@.subrange(0, commands.len() as int) =~= commands@);
    }
    
    count
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
    /* code modified by LLM (iteration 5): added precondition requirement */
    if commands.len() >= usize::MAX {
        return 0;
    }
    
    let left_count = count_char_imperative(&commands, 'L');
    let right_count = count_char_imperative(&commands, 'R');
    let up_count = count_char_imperative(&commands, 'U');
    let down_count = count_char_imperative(&commands, 'D');
    
    let horizontal_min = if left_count <= right_count { left_count } else { right_count };
    let vertical_min = if up_count <= down_count { up_count } else { down_count };
    
    proof {
        count_char_properties(commands@, 'L');
        count_char_properties(commands@, 'R');
        count_char_properties(commands@, 'U');
        count_char_properties(commands@, 'D');
        count_char_bounded(commands@, 'L');
        count_char_bounded(commands@, 'R');
        count_char_bounded(commands@, 'U');
        count_char_bounded(commands@, 'D');
        min_properties(left_count as int, right_count as int);
        min_properties(up_count as int, down_count as int);
        assert(horizontal_min <= commands.len() / 2);
        assert(vertical_min <= commands.len() / 2);
    }
    
    let result = 2 * horizontal_min + 2 * vertical_min;
    
    proof {
        assert(horizontal_min as int == min(left_count as int, right_count as int));
        assert(vertical_min as int == min(up_count as int, down_count as int));
        assert(left_count as int == count_char(commands@, 'L'));
        assert(right_count as int == count_char(commands@, 'R'));
        assert(up_count as int == count_char(commands@, 'U'));
        assert(down_count as int == count_char(commands@, 'D'));
    }
    
    result
}
// </vc-code>


}

fn main() {}