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
/* helper modified by LLM (iteration 5): Fixed count_char_append proof to correctly handle recursive structure */
proof fn count_char_empty(c: char)
    ensures count_char(Seq::<char>::empty(), c) == 0
{
}

proof fn count_char_append(s: Seq<char>, x: char, c: char)
    ensures count_char(s.push(x), c) == count_char(s, c) + if x == c { 1int } else { 0int }
    decreases s.len()
{
    if s.len() == 0 {
        assert(s.push(x) =~= Seq::<char>::new(1, |i| x));
        assert(count_char(s.push(x), c) == if s.push(x)[0] == c { 1int } else { 0int });
        assert(s.push(x)[0] == x);
    } else {
        let s_push = s.push(x);
        assert(s_push.len() == s.len() + 1);
        assert(s_push[0] == s[0]);
        assert(s_push.subrange(1, s_push.len() as int) =~= s.subrange(1, s.len() as int).push(x));
        count_char_append(s.subrange(1, s.len() as int), x, c);
        assert(count_char(s_push.subrange(1, s_push.len() as int), c) == count_char(s.subrange(1, s.len() as int), c) + if x == c { 1int } else { 0int });
    }
}

proof fn count_char_subrange_extend(commands: Seq<char>, i: int, c: char)
    requires 0 <= i < commands.len()
    ensures count_char(commands.subrange(0, i + 1), c) == count_char(commands.subrange(0, i), c) + if commands[i] == c { 1int } else { 0int }
{
    assert(commands.subrange(0, i + 1) =~= commands.subrange(0, i).push(commands[i]));
    count_char_append(commands.subrange(0, i), commands[i], c);
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
    /* code modified by LLM (iteration 5): no changes needed to implementation code */
    let mut left_count: usize = 0;
    let mut right_count: usize = 0;
    let mut up_count: usize = 0;
    let mut down_count: usize = 0;
    let mut i: usize = 0;
    
    while i < n
        invariant
            0 <= i <= n,
            n == commands@.len(),
            valid_commands(commands@),
            left_count <= i,
            right_count <= i,
            up_count <= i,
            down_count <= i,
            left_count + right_count + up_count + down_count <= i,
            left_count as int == count_char(commands@.subrange(0, i as int), 'L'),
            right_count as int == count_char(commands@.subrange(0, i as int), 'R'),
            up_count as int == count_char(commands@.subrange(0, i as int), 'U'),
            down_count as int == count_char(commands@.subrange(0, i as int), 'D'),
        decreases n - i
    {
        let c = commands[i];
        
        proof {
            count_char_subrange_extend(commands@, i as int, 'L');
            count_char_subrange_extend(commands@, i as int, 'R');
            count_char_subrange_extend(commands@, i as int, 'U');
            count_char_subrange_extend(commands@, i as int, 'D');
        }
        
        if c == 'L' {
            assert(left_count < n);
            left_count = left_count + 1;
        } else if c == 'R' {
            assert(right_count < n);
            right_count = right_count + 1;
        } else if c == 'U' {
            assert(up_count < n);
            up_count = up_count + 1;
        } else if c == 'D' {
            assert(down_count < n);
            down_count = down_count + 1;
        }
        i = i + 1;
    }
    
    assert(commands@.subrange(0, n as int) =~= commands@);
    
    let horizontal_pairs = if left_count <= right_count { left_count } else { right_count };
    let vertical_pairs = if up_count <= down_count { up_count } else { down_count };
    
    assert(horizontal_pairs <= n);
    assert(vertical_pairs <= n);
    assert(2 * horizontal_pairs <= 2 * n);
    assert(2 * vertical_pairs <= 2 * n);
    
    let result = 2 * horizontal_pairs + 2 * vertical_pairs;
    result
}
// </vc-code>


}

fn main() {}